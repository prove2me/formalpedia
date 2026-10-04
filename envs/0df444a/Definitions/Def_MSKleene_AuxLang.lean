-- Prove2me | Definitions.Def_MSKleene_AuxLang
-- name    : MSKleene_AuxLang
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:29:36.380271+00:00
-- url     : https://prove2.me/theorems/453d3cb0-8c07-4e76-a084-ff8a39d61fca
-- title:
--   Recognition context and the auxiliary languages $L_u(C,K,l)$
-- statement:
--   The **recognition context** `KleeneCtx` and the **auxiliary languages** $L_u(C,K,l)$ of the proof of Proposition 4.10; the object of the Main Claim (Claim 4.13).
--
--   A `KleeneCtx` packages the data produced at the start of that proof: a state-count function $n : S \to \mathbb{N}$ so the finite recognizing algebra $N$ has carrier $s \mapsto \mathrm{Fin}(n_s)$ with operations `Nop`; the recognizing map `fgen` on generators, extending to $f^{\sharp} : \mathbf{T}_\Sigma(X) \to N$; and, derived from these, $Z = X \cup N$ (`extVars`), the map $h : Z \to N$ that is $f^{\sharp}$ on $X$ and the identity on $N$, and $h^{\sharp} : \mathbf{T}_\Sigma(Z) \to N$.
--
--   For $u \in S$, a set $C \subseteq N$ of leaf-admissible states, a sortwise budget $K \le N$ (where $K_t$ is read as the set $\{0,\dots,K_t-1\}$ of state values still admissible at internal subterms), and a target state $l \in N_u$, `auxLang u C K l` is the set of terms $P \in \mathrm{T}_\Sigma(Z)_u$ such that (a) $P \in \mathrm{T}_\Sigma(X \cup C)$; (b) every proper non-minimal subterm $Q$ of $P$ with variables in $X \cup C$ has $h^{\sharp}(Q) < K$ at its sort; (c) $h^{\sharp}(P) = l$.
--
--   `Term.varsIn` is the predicate 'every variable of the term satisfies a given condition'.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
The recognition context and the auxiliary languages `L_u(C,K,l)` of the proof
of Proposition 4.10 (`PRectoReg`); the object of the Main Claim (Claim 4.13).

A `KleeneCtx` packages the data produced at the start of that proof:
  * `n : S → ℕ`, so the finite recognizing algebra `N` has carrier
    `s ↦ Fin (n s)` and operations `Nop`;
  * `fgen`, the recognizing map on generators, extending to `f^♯ : T_Σ(X) → N`;
  * from these, `Z = X ∪ N` (`extVars`), the map `h : Z → N` with
    `h(x) = f^♯(x)` on `X` and `h = id` on `N`, and `h^♯ : T_Σ(Z) → N`.

For `u ∈ S`, `C ⊆ N` (states allowed at leaves), a sortwise budget
`K ≤ N` (`K t` = the set `{0,…,K t−1}` of state values still admissible at
internal subterms), and `l ∈ N_u`, `auxLang u C K l` is the set of terms
`P ∈ T_Σ(Z)_u` with: (a) `P ∈ T_Σ(X ∪ C)`; (b) every proper non-minimal
subterm `Q` of `P` (with variables in `X ∪ C`) has `h^♯(Q) < K`; (c) `h^♯(P) = l`.

The whole file works at sort universe `0`, matching the mission's theorem
statements (`S : Type`), because the recognizing algebra has carrier `Fin (n s)`.
-/
import Definitions.Def_MSKleene_Subterm
import Definitions.Def_MSKleene_RegAlgebra
import Definitions.Def_MSKleene_Regular

namespace MSKleene

variable {S : Type} {sig : Signature S} {X : SSet S}

-- `Term.varsIn pred P` — every variable occurring in `P` satisfies `pred`.
mutual
def Term.varsIn (pred : (t : S) → X t → Prop) : {s : S} → Term sig X s → Prop
  | _, .var x => pred _ x
  | _, .app _ ts => TermVec.varsAllIn pred ts
def TermVec.varsAllIn (pred : (t : S) → X t → Prop) :
    {w : List S} → TermVec sig X w → Prop
  | _, .nil => True
  | _, .cons t ts => Term.varsIn pred t ∧ TermVec.varsAllIn pred ts
end

/-- The data extracted at the start of the proof of Proposition 4.10: a finite
recognizing algebra `N` with carrier `s ↦ Fin (n s)`, and a recognizing map
`fgen` on the generators. -/
structure KleeneCtx (sig : Signature S) (X : SSet S) where
  /-- state counts: `N_s = Fin (n s)`. -/
  n : S → ℕ
  /-- operations of the finite recognizing algebra `N`. -/
  Nop : {w : List S} → {s : S} → sig w s → Args (fun s => Fin (n s)) w → Fin (n s)
  /-- the recognizing map on generators, `X → N`. -/
  fgen : SMap X (fun s => Fin (n s))

namespace KleeneCtx

variable (ctx : KleeneCtx sig X)

/-- The finite recognizing algebra `N`. -/
def NAlg : Algebra sig := ⟨fun s => Fin (ctx.n s), ctx.Nop⟩

/-- The set of variables `Z = X ∪ N` of the proof. -/
def Z : SSet S := extVars X (fun s => Fin (ctx.n s))

/-- The recognizing homomorphism `f^♯ : T_Σ(X) → N`. -/
def fHom : Hom (freeAlgebra sig X) ctx.NAlg := evalHom ctx.NAlg ctx.fgen

/-- The assignment `h : Z → N`: `h(x) = f^♯(x)` on `X`, `h = id` on `N`. -/
def hAssign : SMap ctx.Z (fun s => Fin (ctx.n s)) :=
  fun s z => Sum.elim (ctx.fgen s) id z

/-- The homomorphism `h^♯ : T_Σ(Z) → N`. -/
def hHom : Hom (freeAlgebra sig ctx.Z) ctx.NAlg := evalHom ctx.NAlg ctx.hAssign

/-- `h^♯` of a sorted term, as a natural number (its state value). -/
def hVal (Q : STerm sig ctx.Z) : ℕ := (ctx.hHom.toFun Q.1 Q.2).val

/-- `P` has variables only in `X ∪ C` (states from `C` allowed at leaves). -/
def inXC (C : (s : S) → Set (Fin (ctx.n s))) (t : S) (z : ctx.Z t) : Prop :=
  Sum.elim (fun _ => True) (fun m => m ∈ C t) z

/-- The auxiliary language `L_u(C,K,l)` (proof of Proposition 4.10). -/
def auxLang (u : S) (C : (s : S) → Set (Fin (ctx.n s))) (K : S → ℕ)
    (l : Fin (ctx.n u)) : Set (Term sig ctx.Z u) :=
  { P |
    Term.varsIn (ctx.inXC C) P ∧
    (∀ Q : STerm sig ctx.Z, SubtermLT Q ⟨u, P⟩ → ¬ Min Q →
      Term.varsIn (ctx.inXC C) Q.2 → ctx.hVal Q < K Q.1) ∧
    ctx.hHom.toFun u P = l }

end KleeneCtx

end MSKleene


