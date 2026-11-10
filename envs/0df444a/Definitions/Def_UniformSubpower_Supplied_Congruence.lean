-- Prove2me | Definitions.Def_UniformSubpower_Supplied_Congruence
-- name    : UniformSubpower_Supplied_Congruence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:20:38.912121+00:00
-- url     : https://prove2.me/theorems/f89ba486-e68a-4554-ba2b-ad3957213c07
-- title:
--   Congruences, the term condition, canonical SI variables, monoliths, centralizers, coarse classes and upward-closed sets
-- statement:
--   Let $A$ be an algebra and $P \subseteq A$ a subuniverse. A **congruence** of $P$ is represented by a relation $\theta$ on $A$ that is supported on $P$, is an equivalence relation on $P$, and is compatible with every basic operation; congruences are ordered by inclusion. $\theta$ is **proper meet-irreducible** ($\theta \in \mathrm{MI}(P)$) when it is not the total relation on $P$ and is not the intersection of two congruences of $P$ both different from it.
--
--   The **term condition** $C(\alpha, \beta; \delta)$ holds when for every term $t(\bar x, \bar y)$ of the original signature and all tuples $\bar a\ \alpha\ \bar b$, $\bar c\ \beta\ \bar d$,
--   $$t(\bar a, \bar c)\ \delta\ t(\bar a, \bar d) \ \Longrightarrow\ t(\bar b, \bar c)\ \delta\ t(\bar b, \bar d).$$
--   For $\theta \in \mathrm{MI}(P)$ the quotient $P/\theta$ is subdirectly irreducible; its **monolith** is represented by the intersection $\mu$ of all congruences of $P$ that contain $\theta$ and differ from it, and its **monolith centralizer** $\rho = (0 : \mu)$, formula (6), by the join (transitive closure of the union) of all congruences $\alpha \supseteq \theta$ of $P$ with $C(\mu, \alpha; \theta)$. The monolith is **abelian** when $C(\mu, \mu; \theta)$.
--
--   Now let $A_i$ ($i \in \iota$) be algebras in one signature, $G \subseteq \prod_i A_i$ and $B = \mathrm{Sg}(G)$, with coordinate projections $P_i = \mathrm{pr}_i(B)$. The **canonical SI variables** are the pairs $w = (i, \theta)$ with $\theta \in \mathrm{MI}(P_i)$, forming the set $W$; $S_w = P_i/\theta$, with monolith $\mu_w$ and centralizer $\rho_w$. An **assignment** gives each variable $w = (i, \theta)$ a value $a_w \in A_i$, read as the class $a_w/\theta$; it lies in $\widehat B_U = \mathrm{pr}_U(\widehat B)$ when one $b \in B$ has $b_i\ \theta\ a_w$ for every $w = (i, \theta) \in U$. Its **singleton/pair tests** on $U$ are membership of its restrictions to all sets $\{v, w\} \subseteq U$. For abelian-monolith $v = (i, \theta)$, $w = (j, \theta')$, $v \sim_{gr} w$ when the projection of $\widehat B$ onto $S_v/\rho_v \times S_w/\rho_w$ is the graph of a bijection, i.e. $b_i\ \rho_v\ b'_i \iff b_j\ \rho_w\ b'_j$ for all $b, b' \in B$; the **coarse classes** are the $\sim_{gr}$-classes of abelian-monolith variables. $U \subseteq W$ is **upward closed** when $(i, \theta) \in U$ and $\theta \subseteq \psi \in \mathrm{MI}(P_i)$ imply $(i, \psi) \in U$.
--
--   **Formalization Note.** A class of $S_w$ is represented by any of its elements, so an assignment is a function giving each candidate variable a value in its coordinate carrier (values off $U$ are ignored); every notion is invariant under the choice of representatives.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), pp. 11–17, §3, §4.1, §4.4, §5.1, §5.2, (5), (6)

import Mathlib
import Definitions.Def_UniformSubpower_Supplied_Algebra

namespace UniformSubpower.Supplied

section Congruences

variable {σ : Signature} {A : Type}

/-- `θ` is a congruence of the subalgebra with universe `P` of `alg`: a relation supported on
`P`, an equivalence relation on `P`, and compatible with every basic operation. -/
def IsConOn (alg : Alg σ A) (P : Set A) (θ : A → A → Prop) : Prop :=
  (∀ x y, θ x y → x ∈ P ∧ y ∈ P) ∧ (∀ x ∈ P, θ x x) ∧ (∀ x y, θ x y → θ y x) ∧
    (∀ x y z, θ x y → θ y z → θ x z) ∧
    ∀ (j : σ.Sym) (a b : Fin (σ.ar j) → A), (∀ k, θ (a k) (b k)) → θ (alg.op j a) (alg.op j b)

/-- The order of the congruence lattice: inclusion of relations. -/
def RelLe (α β : A → A → Prop) : Prop := ∀ x y, α x y → β x y

/-- `θ` is a proper meet-irreducible congruence of `P` (an element of `MI(P)`): a congruence
other than the total relation on `P` that is not the meet (intersection) of two congruences
both different from it. -/
def IsMI (alg : Alg σ A) (P : Set A) (θ : A → A → Prop) : Prop :=
  IsConOn alg P θ ∧ (∃ x ∈ P, ∃ y ∈ P, ¬ θ x y) ∧
    ∀ α β, IsConOn alg P α → IsConOn alg P β → (∀ x y, θ x y ↔ α x y ∧ β x y) → α = θ ∨ β = θ

/-- The term condition `C(α, β; δ)` of Freese–McKenzie (§4.4, p. 16): for every term
`t(x̄, ȳ)` of the original signature and all tuples `ā α b̄`, `c̄ β d̄`,
`t(ā, c̄) δ t(ā, d̄)` implies `t(b̄, c̄) δ t(b̄, d̄)`. -/
def TermCond (alg : Alg σ A) (α β δ : A → A → Prop) : Prop :=
  ∀ (p q : ℕ) (t : Term σ (Fin p ⊕ Fin q)) (a b : Fin p → A) (c d : Fin q → A),
    (∀ k, α (a k) (b k)) → (∀ k, β (c k) (d k)) →
    δ (t.eval alg (Sum.elim a c)) (t.eval alg (Sum.elim a d)) →
    δ (t.eval alg (Sum.elim b c)) (t.eval alg (Sum.elim b d))

/-- The monolith of the quotient `P/θ`, as a congruence of `P` above `θ`: the intersection of all
congruences of `P` that contain `θ` and differ from it. -/
def monolith (alg : Alg σ A) (P : Set A) (θ : A → A → Prop) : A → A → Prop :=
  fun x y => x ∈ P ∧ y ∈ P ∧
    ∀ ψ, IsConOn alg P ψ → RelLe θ ψ → ψ ≠ θ → ψ x y

/-- The monolith centralizer `ρ = (0 : μ)` of the quotient `P/θ`, formula (6), p. 16, as a
congruence of `P` above `θ`: the join of all congruences `α ≥ θ` of `P` with `C(μ, α; θ)`
(that is, `C(μ/θ, α/θ; 0)` in `P/θ`). The join is the transitive closure of the union. -/
def centralizer (alg : Alg σ A) (P : Set A) (θ μ : A → A → Prop) : A → A → Prop :=
  Relation.TransGen
    (fun x y => ∃ α, IsConOn alg P α ∧ RelLe θ α ∧ TermCond alg μ α θ ∧ α x y)

end Congruences

section SIData

variable {σ : Signature} {ι : Type} {A : ι → Type}

/-- The coordinate projection `Pᵢ = prᵢ(B)` of `B = Sg(G)` (§4.1, p. 12). -/
def coordProj (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (i : ι) : Set (A i) :=
  {a | ∃ b ∈ Sg alg G, b i = a}

/-- Candidate SI variables: pairs `(i, θ)` of an original coordinate and a relation on `Aᵢ`. -/
abbrev SIVar (A : ι → Type) : Type := Σ i : ι, (A i → A i → Prop)

/-- The canonical SI index set `W = {(i, θ) : θ ∈ MI(Pᵢ)}`, (5), p. 15. -/
def canonW (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) : Set (SIVar A) :=
  {w | IsMI (alg w.1) (coordProj alg G w.1) w.2}

/-- The monolith `μ_w` of `S_w = P_i/θ` for `w = (i, θ)`. -/
def monoW (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (w : SIVar A) :
    A w.1 → A w.1 → Prop :=
  monolith (alg w.1) (coordProj alg G w.1) w.2

/-- The monolith centralizer `ρ_w = (0 : μ_w)` of `S_w`. -/
def rhoW (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (w : SIVar A) :
    A w.1 → A w.1 → Prop :=
  centralizer (alg w.1) (coordProj alg G w.1) w.2 (monoW alg G w)

/-- `S_w` has an abelian monolith: `C(μ_w, μ_w; 0)` in `S_w`. -/
def AbelianMono (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (w : SIVar A) : Prop :=
  TermCond (alg w.1) (monoW alg G w) (monoW alg G w) w.2

/-- An assignment `a_U` of SI values on `U` (each value `a w ∈ A_i` represents the class
`a w / θ` of `S_w`; values off `U` are ignored) belongs to `B̂_U = pr_U(B̂)`: one `b ∈ B`
has `bᵢ / θ = a w` for every `w = (i, θ) ∈ U`. -/
def InHatB (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (U : Set (SIVar A))
    (a : ∀ w : SIVar A, A w.1) : Prop :=
  ∃ b ∈ Sg alg G, ∀ w ∈ U, w.2 (b w.1) (a w)

/-- The singleton/pair tests of an assignment on `U`: its restriction to every set of at most two
members of `U` lies in the corresponding projection of `B̂`. -/
def PairTests (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (U : Set (SIVar A))
    (a : ∀ w : SIVar A, A w.1) : Prop :=
  ∀ v ∈ U, ∀ w ∈ U, InHatB alg G {v, w} a

/-- `v ∼gr w` (§5.1, p. 16): the actual projection of `B̂` onto `S_v/ρ_v × S_w/ρ_w` is the graph
of a bijection, i.e. for all `b, b' ∈ B`, `b_{i} ρ_v b'_{i}` iff `b_{j} ρ_w b'_{j}`
(`v = (i, θ)`, `w = (j, θ')`). -/
def GraphRel (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (v w : SIVar A) : Prop :=
  ∀ b ∈ Sg alg G, ∀ b' ∈ Sg alg G, rhoW alg G v (b v.1) (b' v.1) ↔ rhoW alg G w (b w.1) (b' w.1)

/-- A coarse class: a `∼gr`-class of the abelian-monolith indices of `W`. -/
def IsCoarseClass (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (F : Set (SIVar A)) : Prop :=
  ∃ v ∈ canonW alg G, AbelianMono alg G v ∧
    F = {w | w ∈ canonW alg G ∧ AbelianMono alg G w ∧ GraphRel alg G v w}

/-- `U ⊆ W` is upward closed (§5.2, p. 17): `(i, θ) ∈ U` and `θ ≤ ψ ∈ MI(Pᵢ)` imply
`(i, ψ) ∈ U`. -/
def UpwardClosed (alg : ∀ i, Alg σ (A i)) (G : Set (∀ i, A i)) (U : Set (SIVar A)) : Prop :=
  U ⊆ canonW alg G ∧
    ∀ (i : ι) (θ ψ : A i → A i → Prop), (⟨i, θ⟩ : SIVar A) ∈ U → RelLe θ ψ →
      (⟨i, ψ⟩ : SIVar A) ∈ canonW alg G → (⟨i, ψ⟩ : SIVar A) ∈ U

end SIData

end UniformSubpower.Supplied


