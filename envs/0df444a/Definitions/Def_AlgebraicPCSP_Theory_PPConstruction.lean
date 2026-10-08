-- Prove2me | Definitions.Def_AlgebraicPCSP_Theory_PPConstruction
-- name    : AlgebraicPCSP_Theory_PPConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:50.609856+00:00
-- url     : https://prove2.me/theorems/025e9f2f-2da6-46a0-b9b0-df08d9f482fd
-- title:
--   pp-formulas, pp-powers, homomorphic relaxations and pp-constructibility (Definitions 2.23, 2.24, 4.6, 4.7, 4.9)
-- statement:
--   **pp-formulas (Definition 2.23).** A *primitive positive formula* over a signature is an existentially quantified conjunction of finitely many atomic predicates $(v_{j_1},\dots,v_{j_k})\in R$, with $k=\mathrm{ar}(R)$, and equalities $v_{j_1}=v_{j_2}$. For a structure $\mathbf A$, $\Psi^{\mathbf A}$ is the formula with each symbol $R$ read as $R^{\mathbf A}$; its satisfying assignments of the free variables form a relation on $A$.
--
--   **pp-powers (Definitions 2.24(1) and 4.7).** Let $(\mathbf A,\mathbf B)$ and $(\mathbf A',\mathbf B')$ be PCSP templates. $(\mathbf A',\mathbf B')$ is an *$n$-th pp-power* of $(\mathbf A,\mathbf B)$ if $A'=A^n$, $B'=B^n$, and, viewing each $k$-ary relation on $A^n$ (resp. $B^n$) as a $kn$-ary relation on $A$ (resp. $B$), for every relation symbol $R$ of $(\mathbf A',\mathbf B')$ there is a single pp-formula $\Psi_R$ over the signature of $(\mathbf A,\mathbf B)$ with
--   $$R^{\mathbf A'}=\{\mathbf t\mid \Psi_R^{\mathbf A}(\mathbf t)\},\qquad R^{\mathbf B'}=\{\mathbf t\mid \Psi_R^{\mathbf B}(\mathbf t)\}.$$
--
--   **Homomorphic relaxations (Definition 4.6).** For similar PCSP templates, $(\mathbf A',\mathbf B')$ is a *(homomorphic) relaxation* of $(\mathbf A,\mathbf B)$ if there are homomorphisms $h_A:\mathbf A'\to\mathbf A$ and $h_B:\mathbf B\to\mathbf B'$.
--
--   **pp-constructibility (Definition 4.9).** $(\mathbf A',\mathbf B')$ is *pp-constructible* from $(\mathbf A,\mathbf B)$ if there is a finite sequence of templates
--   $$(\mathbf A,\mathbf B)=(\mathbf A_1,\mathbf B_1),\dots,(\mathbf A_k,\mathbf B_k)=(\mathbf A',\mathbf B')$$
--   in which each $(\mathbf A_{i+1},\mathbf B_{i+1})$ is a pp-power or a homomorphic relaxation of $(\mathbf A_i,\mathbf B_i)$.
--
--   These relational constructions are the right-hand side of Theorem 4.12: they are exactly the ways to obtain a template whose polymorphism minion receives a minion homomorphism from $\mathrm{Pol}(\mathbf A,\mathbf B)$.
--
--   **Formalization Note** A pp-formula with free variables $X$ has a finite type $Y$ of quantified variables, finitely many atoms (a symbol and its argument variables in $X\oplus Y$) and finitely many equalities. In a pp-power the free variables of $\Psi_R$ are indexed by $[\mathrm{ar}(R)]\times[n]$: the pair $(i,j)$ is the $j$-th coordinate of the $i$-th entry. The same formula defines $R^{\mathbf A'}$ and $R^{\mathbf B'}$. A pp-power of exponent $n=0$ is not excluded, as the paper does not exclude it. Since signatures and domains change along a sequence, a template is bundled (`Template`) with a finite signature, arities $\ge1$ and finite domains with decidable equality, the paper's standing assumptions (Definition 2.2), and nonempty domains, the field's standing convention (the paper identifies a domain with $[n]$). A relaxation step therefore also requires nonempty new domains. `PPConstructible T T'` is the inductive closure of $T$ under appending a pp-power step or a relaxation step. A relaxation step requires its new pair to be a PCSP template, as Definition 4.6 does; a pp-power of a PCSP template is automatically one.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 14 (Definitions 2.23, 2.24), p. 25 (Definitions 4.6, 4.7), p. 26 (Definition 4.9)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.Theory

open PCSPBLPAff.Symmetric

/-- A primitive positive formula (Definition 2.23, p. 14) over the signature `(τ, ar)` with free
variables `X`: an existentially quantified conjunction of atomic predicates
`(v_{j₁}, …, v_{j_k}) ∈ R` (`k = ar R`) and equalities `v_{j₁} = v_{j₂}`. The quantified
variables form the finite type `Y`; the variables of the atoms and equalities range over
`X ⊕ Y`; there are finitely many atoms and equalities. -/
structure PPFormula (τ : Type) (ar : τ → ℕ) (X : Type) where
  /-- The existentially quantified variables. -/
  Y : Type
  [finY : Finite Y]
  /-- Index set of the atomic predicates `(v_{j₁}, …, v_{j_k}) ∈ R`. -/
  Atom : Type
  [finAtom : Finite Atom]
  /-- The relation symbol `R` of each atom. -/
  atomSym : Atom → τ
  /-- The variables `(v_{j₁}, …, v_{j_k})` of each atom. -/
  atomArgs : (a : Atom) → Fin (ar (atomSym a)) → X ⊕ Y
  /-- Index set of the equalities `v_{j₁} = v_{j₂}`. -/
  Eqn : Type
  [finEqn : Finite Eqn]
  /-- The two sides of each equality. -/
  eqns : Eqn → (X ⊕ Y) × (X ⊕ Y)

/-- `Ψ^𝔸(a)`: the pp-formula `Ψ`, with each symbol `R` interpreted as `R^𝔸`, holds at the
assignment `a : X → A` of its free variables (Definition 2.23, p. 14): some assignment
`b : Y → A` of the quantified variables makes every atom and every equality true. -/
def PPFormula.Holds {τ : Type} {ar : τ → ℕ} {X A : Type} (Ψ : PPFormula τ ar X)
    (𝔸 : RelStruct τ ar A) (a : X → A) : Prop :=
  ∃ b : Ψ.Y → A,
    (∀ t : Ψ.Atom, (fun j => Sum.elim a b (Ψ.atomArgs t j)) ∈ 𝔸.rel (Ψ.atomSym t)) ∧
    ∀ q : Ψ.Eqn, Sum.elim a b (Ψ.eqns q).1 = Sum.elim a b (Ψ.eqns q).2

/-- `(𝔸', 𝔹')` (signature `(τ', ar')`) is an `n`-th pp-power of `(𝔸, 𝔹)` (signature `(τ, ar)`)
(Definition 4.7, p. 25, with Definition 2.24(1), p. 14): `A' = Aⁿ`, `B' = Bⁿ`, and for every
symbol `R` of `τ'`, viewing a `k`-tuple of elements of `Aⁿ` (resp. `Bⁿ`), `k = ar' R`, as a
`kn`-tuple over `A` (resp. `B`) indexed by `[k] × [n]`, there is **one** pp-formula `Ψ_R`
over `(τ, ar)` such that `R^{𝔸'} = {t | Ψ_R^𝔸(t)}` and `R^{𝔹'} = {t | Ψ_R^𝔹(t)}`. -/
def IsPPPower {τ τ' : Type} {ar : τ → ℕ} {ar' : τ' → ℕ} {A B : Type} (n : ℕ)
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (𝔸' : RelStruct τ' ar' (Fin n → A)) (𝔹' : RelStruct τ' ar' (Fin n → B)) : Prop :=
  ∀ R : τ', ∃ Ψ : PPFormula τ ar (Fin (ar' R) × Fin n),
    (∀ t : Fin (ar' R) → Fin n → A, t ∈ 𝔸'.rel R ↔ Ψ.Holds 𝔸 (fun p => t p.1 p.2)) ∧
    (∀ t : Fin (ar' R) → Fin n → B, t ∈ 𝔹'.rel R ↔ Ψ.Holds 𝔹 (fun p => t p.1 p.2))

/-- `(𝔸', 𝔹')` is a homomorphic relaxation of the similar template `(𝔸, 𝔹)` (Definition 4.6,
p. 25): there are homomorphisms `h_A : 𝔸' → 𝔸` and `h_B : 𝔹 → 𝔹'`. -/
def IsRelaxation {τ : Type} {ar : τ → ℕ} {A B A' B' : Type} (𝔸 : RelStruct τ ar A)
    (𝔹 : RelStruct τ ar B) (𝔸' : RelStruct τ ar A') (𝔹' : RelStruct τ ar B') : Prop :=
  (∃ hA : A' → A, IsHom 𝔸' 𝔸 hA) ∧ (∃ hB : B → B', IsHom 𝔹 𝔹' hB)

/-- A pair `(𝔸, 𝔹)` of similar finite structures, bundled with its signature and domains so
that a sequence of pairs may change them (used in Definition 4.9, p. 26). The signature is
finite, all arities are `≥ 1` and both domains are finite (standing assumptions of
Definition 2.2, p. 8) and nonempty (the standing convention that the domain of a structure is
nonempty, used when the paper identifies a domain with `[n]`). -/
structure Template : Type 1 where
  /-- The signature (relation symbols). -/
  τ : Type
  /-- The arities. -/
  ar : τ → ℕ
  /-- The domain of `𝔸`. -/
  A : Type
  /-- The domain of `𝔹`. -/
  B : Type
  [instτ : Fintype τ]
  [instA : Fintype A]
  [instDecA : DecidableEq A]
  [instB : Fintype B]
  [instDecB : DecidableEq B]
  [instNeA : Nonempty A]
  [instNeB : Nonempty B]
  ar_pos : ∀ R, 0 < ar R
  /-- The first structure. -/
  𝔸 : RelStruct τ ar A
  /-- The second structure. -/
  𝔹 : RelStruct τ ar B

attribute [instance] Template.instτ Template.instA Template.instDecA Template.instB
  Template.instDecB Template.instNeA Template.instNeB

/-- Bundle a pair of similar finite structures as a `Template`. -/
def Template.of {τ : Type} [Fintype τ] {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Nonempty A] [Nonempty B] (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (har : ∀ R, 0 < ar R) : Template :=
  { τ := τ, ar := ar, A := A, B := B, ar_pos := har, 𝔸 := 𝔸, 𝔹 := 𝔹 }

/-- `T'` is pp-constructible from `T` (Definition 4.9, p. 26): there is a finite sequence
`T = T₁, …, T_k = T'` of templates in which each `T_{i+1}` is a pp-power of `T_i`
(Definition 4.7) or a homomorphic relaxation of `T_i` (Definition 4.6). The reflexive-transitive
closure is generated by appending one step at the end. A relaxation step requires the new pair
to be a PCSP template (`A'' → B''`), as Definition 4.6 assumes; a pp-power of a PCSP template is
one automatically. -/
inductive PPConstructible (T : Template) : Template → Prop
  /-- The one-element sequence. -/
  | refl : PPConstructible T T
  /-- Append an `n`-th pp-power of the last template. -/
  | power {T' : Template} (hT' : PPConstructible T T') (n : ℕ) (τ'' : Type) [Fintype τ'']
      (ar'' : τ'' → ℕ) (har'' : ∀ R, 0 < ar'' R)
      (𝔸'' : RelStruct τ'' ar'' (Fin n → T'.A)) (𝔹'' : RelStruct τ'' ar'' (Fin n → T'.B))
      (hpow : @IsPPPower T'.τ τ'' T'.ar ar'' T'.A T'.B n T'.𝔸 T'.𝔹 𝔸'' 𝔹'') :
      PPConstructible T
        (Template.of (A := Fin n → T'.A) (B := Fin n → T'.B) 𝔸'' 𝔹'' har'')
  /-- Append a homomorphic relaxation `(𝔸'', 𝔹'')` of the last template. -/
  | relax {T' : Template} (hT' : PPConstructible T T') (A'' B'' : Type) [Fintype A'']
      [DecidableEq A''] [Fintype B''] [DecidableEq B''] [Nonempty A''] [Nonempty B'']
      (𝔸'' : RelStruct T'.τ T'.ar A'') (𝔹'' : RelStruct T'.τ T'.ar B'')
      (htemp : IsPromiseTemplate 𝔸'' 𝔹'') (hrel : IsRelaxation T'.𝔸 T'.𝔹 𝔸'' 𝔹'') :
      PPConstructible T (Template.of 𝔸'' 𝔹'' T'.ar_pos)

end AlgebraicPCSP.Theory


