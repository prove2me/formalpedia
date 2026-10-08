-- Prove2me | Definitions.Def_PCSPBLPAff_Characterization_Setting
-- name    : PCSPBLPAff_Characterization_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:00.205749+00:00
-- url     : https://prove2.me/theorems/dd1cd33f-9d9a-4afb-92f3-31f0ad3610b7
-- title:
--   §2–§5 and App. A — PCSP templates, polymorphisms, the BLP+Affine algorithm, the minion M_BLP+Aff, minion homomorphisms and the free structure
-- statement:
--   This file sets up the objects of Brakensiek, Guruswami, Wrochna and Živný, *The Power of the Combined Basic LP and Affine Relaxation for Promise CSPs*.
--
--   **Structures and templates (§2, p. 4).** A signature $\tau$ assigns to each symbol $R$ an arity $\mathrm{ar}(R)\in\mathbb N$. A relational structure $\mathbf A$ on a domain $A$ consists of relations $R^{\mathbf A}\subseteq A^{\mathrm{ar}(R)}$. A homomorphism $\sigma:\mathbf A\to\mathbf B$ is a map $A\to B$ with $\sigma(R^{\mathbf A})\subseteq R^{\mathbf B}$ for all $R$, applied component-wise; $(\mathbf A,\mathbf B)$ is a **promise template** if such a homomorphism exists.
--
--   **Instances (§2.1).** An instance $X$ has variables $x_1,\dots,x_n$ and constraints $c_j=(R_j,\bar x_j)$, $j\in[m]$, with $\bar x_j$ a tuple of variables of arity $\mathrm{ar}(R_j)$. It is satisfiable in a structure $\mathbf C$ if some assignment sends every $\bar x_j$ into $R_j^{\mathbf C}$.
--
--   **Polymorphisms (§2.2).** $f:A^L\to B$ is a polymorphism of $(\mathbf A,\mathbf B)$ if for every $R$ and every $L\times\mathrm{ar}(R)$ matrix whose rows lie in $R^{\mathbf A}$, applying $f$ to the columns gives a tuple in $R^{\mathbf B}$. It is symmetric if it is invariant under all permutations of its arguments, and block-symmetric for a partition $[L]=B_1\cup\dots\cup B_\kappa$ if it is invariant under permutations preserving every block; it has **width at least $N$** if this holds for some partition into at least one block, each of size at least $N$ (§4, p. 8, footnote 2).
--
--   **The relaxations and the algorithm (§2.3, Figure 1, Definition 1, pp. 5–6).** $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ is the Basic LP (1)–(5): rational $w_i(a)\ge0$ and $p_j(y)\ge0$ ($y\in R_j^{\mathbf A}$), $\sum_a w_i(a)=1$, $\sum_y p_j(y)=1$, and $\sum_{y:\,y_k=a}p_j(y)=w_{i}(a)$ whenever $x_i$ is the $k$-th variable of $\bar x_j$. $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$ is the same linear system (6)–(8) over $\mathbb Z$ without sign constraints, with unknowns $r_i(a)$, $q_j(y)$. The BLP+Affine algorithm accepts $X$ if $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ has a relative interior point $(w,p)$ and the refined lattice $\mathrm{Aff}'_{\mathbb Z}(X,\mathbf A)$ — the solutions $(r,q)$ with $r_i(a)=0$ whenever $w_i(a)=0$ and $q_j(y)=0$ whenever $p_j(y)=0$ — is nonempty. It **correctly solves** $\mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B)$ if it accepts every instance satisfiable in $\mathbf A$ and rejects every instance unsatisfiable in $\mathbf B$.
--
--   **Minors and the minion $\mathcal M_{\mathrm{BLP+Aff}}$ (§5, Eq. (11), Definitions 5–6, p. 10).** The minor of $f:A^L\to B$ along $\pi:[L]\to[L']$ is
--   $$f_{/\pi}(x_1,\dots,x_{L'}) = f(x_{\pi(1)},\dots,x_{\pi(L)}).$$
--   The $L$-ary objects of $\mathcal M_{\mathrm{BLP+Aff}}$ are the pairs $(w,r)$ with $w:[L]\to\mathbb Q_{\ge0}$, $\sum_i w(i)=1$, $r:[L]\to\mathbb Z$, $\sum_i r(i)=1$, and $w(i)=0\Rightarrow r(i)=0$; their minor along $\pi$ is
--   $$w_{/\pi}(i)=\sum_{j\in\pi^{-1}(i)}w(j),\qquad r_{/\pi}(i)=\sum_{j\in\pi^{-1}(i)}r(j).$$
--   A minion homomorphism $\xi:\mathcal M_{\mathrm{BLP+Aff}}\to\mathrm{Pol}(\mathbf A,\mathbf B)$ sends each $L$-ary object to an $L$-ary polymorphism and satisfies $\xi((w,r)_{/\pi})=\xi(w,r)_{/\pi}$ for every $\pi:[L]\to[L']$.
--
--   **The free structure (Definition 12, p. 14).** $F_{\mathcal M_{\mathrm{BLP+Aff}}}(\mathbf A)$ has as domain the objects of $\mathcal M_{\mathrm{BLP+Aff}}$ with coordinate set $A$, the same signature as $\mathbf A$, and $(t_1,\dots,t_k)\in R^F$ iff there is an object $(p,q)$ with coordinate set $R^{\mathbf A}$ such that $t_i=(p,q)_{/\pi_i}$ for every $i\in[k]$, where $\pi_i:R^{\mathbf A}\to A$ is the $i$-th coordinate map.
--
--   **Example 10's digraph (p. 13).** The disjoint union of the directed 2-cycle $0\to1\to0$ and the directed 3-cycle $0'\to1'\to2'\to0'$, as a structure with one binary relation.
--
--   These are the objects of Theorem 4 and of Lemmas 7–9 and 16–17, which characterize exactly the templates that the BLP+Affine algorithm solves.
--
--   **Formalization Note** Variables of an instance are `Fin n` and arities `Fin L`; the paper's positive-arity requirement is dropped (no statement needs it). $p_j$, $q_j$ and the free structure's $(p,q)$ are functions on all tuples $A^k$ that are required to vanish off $R^{\mathbf A}$; this is equivalent to indexing by $R^{\mathbf A}$, since $p(y)=0$ forces $q(y)=0$. The marginal conditions (5) and (8) are imposed for each position $k$ of the scope. The relative interior point is encoded by the property the algorithm uses (footnote 1): a solution whose zero coordinates are exactly those that vanish on the whole polytope. Width requires at least one block. Objects of the free structure are indexed by $A$ itself and the $\pi_i$ are the coordinate maps $y\mapsto y_i$. There is no abstract minion structure: the only minions that occur are $\mathcal M_{\mathrm{BLP+Aff}}$ and $\mathrm{Pol}(\mathbf A,\mathbf B)$, and a minion homomorphism between them is spelled out; the arity of $\xi(w,r)$ is fixed by its type.
-- source:
--   arXiv:1907.04383v3, §2 (p. 4), §2.3 (p. 5), Figure 1 and Definition 1 (p. 6), §4 and footnote 2 (p. 8), Eq. (11), Definitions 5 and 6 (p. 10), Example 10 (p. 13), Definition 12 (p. 14)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace PCSPBLPAff.Characterization

/-! ### Minors, the minion `M_BLP+Aff`, minion homomorphisms and the free structure (§5, App. A) -/

/-- The minor of a rational weight vector along `π : ι → κ` (Definition 6, p. 10):
`w_{/π}(i) = w(π⁻¹(i)) = ∑_{j ∈ π⁻¹(i)} w(j)`. -/
def minorQ {ι κ : Type} [Fintype ι] [DecidableEq κ] (π : ι → κ) (w : ι → ℚ) : κ → ℚ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j => π j = i), w j

/-- The minor of an integer weight vector along `π : ι → κ` (Definition 6, p. 10):
`r_{/π}(i) = r(π⁻¹(i)) = ∑_{j ∈ π⁻¹(i)} r(j)`. -/
def minorZ {ι κ : Type} [Fintype ι] [DecidableEq κ] (π : ι → κ) (r : ι → ℤ) : κ → ℤ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j => π j = i), r j

/-- `(w, r)` is an object of the minion `M_BLP+Aff` with coordinate set `ι` (Definition 6,
p. 10): `w : ι → ℚ≥0` sums to `1`, `r : ι → ℤ` sums to `1`, and `w(i) = 0 ⟹ r(i) = 0`. -/
def IsBLPAffObj {ι : Type} [Fintype ι] (w : ι → ℚ) (r : ι → ℤ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, r i = 1 ∧ ∀ i, w i = 0 → r i = 0

/-- The set of objects of `M_BLP+Aff` with coordinate set `ι`; for `ι = Fin L` this is
`M^{(L)}_BLP+Aff` (Definition 6, p. 10). -/
def BLPAffObj (ι : Type) [Fintype ι] : Type :=
  {x : (ι → ℚ) × (ι → ℤ) // IsBLPAffObj x.1 x.2}

/-- The minor `f_{/π}` of an `L`-ary function `f : A^L → B` along `π : [L] → [L']`, Eq. (11),
p. 10: `f_{/π}(x_1, …, x_{L'}) = f(x_{π(1)}, …, x_{π(L)})`. -/
def polMinor {A B : Type} {L L' : ℕ} (π : Fin L → Fin L') (f : (Fin L → A) → B) :
    (Fin L' → A) → B :=
  fun x => f (x ∘ π)

/-- `ξ` is a minion homomorphism from `M_BLP+Aff` to `Pol(𝔸, 𝔹)` (Definitions 5–6, p. 10):
it sends every `L`-ary object to an `L`-ary polymorphism (arity is preserved by the type of
`ξ`), and it preserves minors, `ξ((w, r)_{/π}) = ξ(w, r)_{/π}` for every `π : [L] → [L']`.
The hypothesis `h` (that the minor is again an object) is only there to form the minor as an
element of `M^{(L')}_BLP+Aff`. -/
def IsMinionHomToPol {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A)
    (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (ξ : (L : ℕ) → BLPAffObj (Fin L) → (Fin L → A) → B) : Prop :=
  ∀ (L : ℕ) (x : BLPAffObj (Fin L)),
    PCSPBLPAff.Symmetric.IsPolymorphism 𝔸 𝔹 (ξ L x) ∧
    ∀ (L' : ℕ) (π : Fin L → Fin L') (h : IsBLPAffObj (minorQ π x.1.1) (minorZ π x.1.2)),
      ξ L' ⟨(minorQ π x.1.1, minorZ π x.1.2), h⟩ = polMinor π (ξ L x)

/-- `M_BLP+Aff` admits a minion homomorphism to `Pol(𝔸, 𝔹)` (§5, p. 11). -/
def HasMinionHomToPol {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A)
    (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) : Prop :=
  ∃ ξ : (L : ℕ) → BLPAffObj (Fin L) → (Fin L → A) → B, IsMinionHomToPol 𝔸 𝔹 ξ

/-- The domain `M^{(|A|)}_BLP+Aff` of the free structure, its objects indexed by `A` itself
(Definition 12, p. 14). -/
abbrev FreeDom (A : Type) [Fintype A] : Type := BLPAffObj A

/-- The free structure `F_{M_BLP+Aff}(𝔸)` (Definition 12, p. 14): domain `M^{(|A|)}_BLP+Aff`;
a tuple `(t_1, …, t_k)` is in `R^F` iff there is an object `(p, q)` of `M_BLP+Aff` with
coordinates `R^A` such that `t_k = (p, q)_{/π_k}` for each position `k`, where
`π_k : R^A → A` is the `k`-th coordinate map. The object `(p, q)` is encoded on all tuples
`A^k` and required to vanish off `R^A`. -/
def freeStruct {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) : PCSPBLPAff.Symmetric.RelStruct τ ar (FreeDom A) where
  rel R := {t | ∃ (p : (Fin (ar R) → A) → ℚ) (q : (Fin (ar R) → A) → ℤ),
    IsBLPAffObj p q ∧ (∀ y, y ∉ 𝔸.rel R → p y = 0) ∧
    ∀ k, (t k).1 = (minorQ (fun y => y k) p, minorZ (fun y => y k) q)}

/-! ### The digraph of Example 10 (p. 13) -/

/-- The arcs of the disjoint union of a directed 2-cycle `{0, 1}` (as `Sum.inl`) and a
directed 3-cycle `{0′, 1′, 2′}` (as `Sum.inr`): `i → i + 1` in each cycle (Example 10, p. 13). -/
def example10Arc : Fin 2 ⊕ Fin 3 → Fin 2 ⊕ Fin 3 → Prop
  | .inl i, .inl j => j = i + 1
  | .inr i, .inr j => j = i + 1
  | _, _ => False

/-- The digraph `A` of Example 10 (p. 13) as a relational structure with one binary symbol. -/
def example10Digraph : PCSPBLPAff.Symmetric.RelStruct Unit (fun _ => 2) (Fin 2 ⊕ Fin 3) where
  rel _ := {t | example10Arc (t 0) (t 1)}

end PCSPBLPAff.Characterization


