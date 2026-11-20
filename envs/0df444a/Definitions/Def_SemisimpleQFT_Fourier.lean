-- Prove2me | Definitions.Def_SemisimpleQFT_Fourier
-- name    : SemisimpleQFT_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-19T15:06:13.431551+00:00
-- url     : https://prove2.me/theorems/f3f6ccf5-7544-4e4f-9592-d219afc36521
-- title:
--   Fourier transform of a semisimple $\mathbb{C}$-algebra: Fourier basis, $\mathrm{FT}_A$, $\widetilde{\mathrm{FT}}_A$, $\delta$-niceness
-- statement:
--   Throughout, $A$ is an associative unital $\mathbb{C}$-algebra.
--
--   **Fourier isomorphism (Definitions 2.4, 2.5, Eq. (2.2)).** A `FourierData A Λ J` is a choice of isomorphism $A \cong \bigoplus_{\rho\in\widehat A} M_{d_\rho}(\mathbb{C})$, $a \mapsto (\rho(a))_\rho$, written as a single block-diagonal matrix representation. $\Lambda=\widehat A$ is the set of irreps; $J$ is a finite set, the disjoint union over $\rho$ of the index sets of the chosen bases of the irrep spaces $V^\rho$; `lab` $: J\to\Lambda$ sends a basis index to its irrep and is surjective (so $d_\rho\ge 1$); `rep` $: A\to M_J(\mathbb{C})$ is an algebra homomorphism with $\mathrm{rep}(a)_{ij}=0$ whenever $\mathrm{lab}(i)\ne\mathrm{lab}(j)$, which is injective and whose image is the set of all block-diagonal matrices. For $\mathrm{lab}(i)=\mathrm{lab}(j)=\rho$ the irrep matrix element is $\rho(a)_{ij}=\mathrm{rep}(a)_{ij}$.
--
--   - `dim ρ` is $d_\rho=\#\{i\in J : \mathrm{lab}(i)=\rho\}$.
--   - `Idx` is the index set of the Fourier basis, $\{(\rho,i,j)\}$, realised as the pairs $(i,j)\in J\times J$ with $\mathrm{lab}(i)=\mathrm{lab}(j)$; `row`, `col` are $i$, $j$.
--   - `E i j` is the Fourier basis element $E^\rho_{ij}$: the unique element with $\mathrm{rep}(E^\rho_{ij})=|i\rangle\langle j|$ when $\mathrm{lab}(i)=\mathrm{lab}(j)$; it is set to $0$ when $\mathrm{lab}(i)\neq\mathrm{lab}(j)$. `EI p` is $E^\rho_{ij}$ for $p=(\rho,i,j)$.
--
--   **Regular trace form and dual bases (Eq. (2.3), Definition 2.8).** `regTrace A a` is $\tau_{\mathbf L}(a)=\mathrm{Tr}(\mathbf L(a))$, the trace of left multiplication by $a$ on $A$. `IsRegDual b bs` says that the family $(a_i^*)=bs$ is dual to the family $(a_i)=b$ for $\langle x,y\rangle_{\mathbf L}=\tau_{\mathbf L}(xy)$: $\tau_{\mathbf L}(a_i^*a_j)=\delta_{ij}$.
--
--   **Computational basis (Definition 2.10).** A `CompBasis A ι` consists of vectors `vec a` ($a\in\iota$) and a linear coordinate map `coord` $:A\to\mathbb{C}^\iota$; no relation between them is imposed by the structure. For a basis $b$ of $A$, `CompBasis.ofBasis b` takes `vec = b` and `coord` the coordinates in $b$. Then
--   $$\langle x,y\rangle_0=\sum_{a\in\iota}\overline{\mathrm{coord}(x)_a}\,\mathrm{coord}(y)_a,\qquad \|x\|_2=\Big(\sum_{a}|\mathrm{coord}(x)_a|^2\Big)^{1/2}.$$
--
--   **Fourier transforms (Definition 3.1, Theorem 3.4, Definition 3.3).** With rows indexed by $(\rho,i,j)$ and columns by $a\in\iota$:
--   $$\mathrm{FT}_{(\rho,i,j),a}=\frac{\langle E^\rho_{ij},\mathrm{vec}(a)\rangle_0}{\|E^\rho_{ij}\|_2},\qquad \widetilde{\mathrm{FT}}_{(\rho,i,j),a}=\|E^\rho_{ij}\|_2\,\rho(\mathrm{vec}(a))_{ij},$$
--   $$G_{(\rho,i,j),(\sigma,k,l)}=\frac{\langle E^\rho_{ij},E^\sigma_{kl}\rangle_0}{\|E^\rho_{ij}\|_2\,\|E^\sigma_{kl}\|_2}.$$
--   `IsNice F c δ` says $\|G-I\|_\infty\le\delta$, where $\|\cdot\|_\infty$ is the operator norm induced by the 2-norm (`QAlgorithms.specNorm`). Division by $0$ returns $0$.
--
--   **Adapted bases (Section 5.2, Eqs. (5.7)–(5.8)).** For subalgebras $B\subseteq A$ of an algebra $R$ with Fourier data $F_A$, $F_B$ and a map $\mathrm{tr}:J_A\to J_B$ (sending the index $k\circ\rho$ to $k$), `IsAdapted` says: for $b\in B$ and $P,Q$ in the same irrep of $A$, $\rho(b)_{P,Q}=\sigma(b)_{\mathrm{tr}P,\mathrm{tr}Q}$ if $\mathrm{tr}P,\mathrm{tr}Q$ lie in the same irrep $\sigma$ of $B$ and $\rho(b)_{P,Q}=0$ otherwise; and, within each irrep $\rho$ of $A$, $\mathrm{tr}$ is injective and its image is a union of full index sets of irreps of $B$ (multiplicity-free branching).
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, Sections 2–3 and 5.2, pp. 14–21 and 32: Definitions 2.4, 2.5, 2.8, 2.10, 3.1, 3.3, Eqs. (2.2), (2.3), (3.4), (3.18), (3.19), (5.7), (5.8)

import Definitions.Def_QAlgorithms_Defs_Basic

/-!
# The Fourier transform of a finite-dimensional semisimple `ℂ`-algebra

Source: B. Foxman, B. Nehoran, Y. Ding, *Efficient Quantum Fourier Transforms For Semisimple
Algebras*, Sections 2 and 3 (PDF pp. 14–21).

Conventions fixed here and used by every statement of the mission:

* `A` is an associative unital `ℂ`-algebra (`[Ring A] [Algebra ℂ A]`).
* A choice of Fourier isomorphism `A ≅ ⊕_ρ M_{d_ρ}(ℂ)` (Definition 2.4, Eq. (2.2)) is a
  `FourierData A Λ J`: `Λ` is the set `Â` of irreps, `J` is the disjoint union over `ρ` of the
  index sets of bases of the irrep spaces `V^ρ`, `lab : J → Λ` says which irrep an index belongs
  to, and `rep a` is the block-diagonal matrix `⊕_ρ ρ(a)`, so that `ρ(a)_{ij} = rep a i j` for
  `lab i = lab j = ρ`.
* The computational basis `𝓑(A)` enters through a `CompBasis`: the family of basis vectors
  together with the linear map sending an element to its coordinates. For a genuine basis `b`
  this is `CompBasis.ofBasis b`.
* `⟨x, y⟩₀` is conjugate-linear in the first argument (PDF p. 16).
* `‖·‖_∞` is the operator norm induced by the 2-norm (PDF p. 53), `QAlgorithms.specNorm`.
-/

namespace SemisimpleQFT

open scoped BigOperators ComplexConjugate

universe u v w x

/-- Definitions 2.4 and 2.5 (PDF p. 15, Eq. (2.2)): a Fourier isomorphism
`A ≅ ⊕_{ρ ∈ Â} M_{d_ρ}(ℂ)`, `a ↦ (ρ(a))_ρ`, written as one block-diagonal matrix
representation. `Λ` is the set `Â` of (labels of) irreps; `J` indexes the union of the bases of
all irrep spaces, `lab i` being the irrep that the basis index `i` belongs to. The matrix of the
irrep `ρ` at `a` is the block `(rep a i j)_{lab i = lab j = ρ}`, of size
`d_ρ = #{i | lab i = ρ}`. The map `rep` is an algebra homomorphism which is zero outside the
diagonal blocks, injective, and onto the block-diagonal matrices; every label is used
(`lab_surjective`), so every `ρ ∈ Λ` has `d_ρ ≥ 1`. -/
structure FourierData (A : Type u) [Ring A] [Algebra ℂ A] (Λ : Type v) (J : Type w)
    [Fintype J] [DecidableEq J] where
  /-- The irrep to which a basis index belongs. -/
  lab : J → Λ
  /-- `a ↦ ⊕_ρ ρ(a)`, as a block-diagonal matrix. -/
  rep : A →ₐ[ℂ] Matrix J J ℂ
  /-- Every irrep label is used: `d_ρ ≥ 1`. -/
  lab_surjective : Function.Surjective lab
  /-- `rep a` is block diagonal. -/
  rep_block : ∀ (a : A) (i j : J), lab i ≠ lab j → rep a i j = 0
  /-- The Fourier map is injective. -/
  rep_injective : Function.Injective rep
  /-- The Fourier map is onto the block-diagonal matrices. -/
  rep_surjective : ∀ M : Matrix J J ℂ, (∀ i j : J, lab i ≠ lab j → M i j = 0) →
    ∃ a : A, rep a = M

namespace FourierData

variable {A : Type u} [Ring A] [Algebra ℂ A] {Λ : Type v} {J : Type w}
  [Fintype J] [DecidableEq J]

/-- The dimension `d_ρ` of the irrep `ρ` (PDF p. 15): the number of basis indices with label
`ρ`. -/
noncomputable def dim (F : FourierData A Λ J) (ρ : Λ) : ℕ :=
  Nat.card {i : J // F.lab i = ρ}

/-- The index set `{(ρ, i, j) : ρ ∈ Â, 1 ≤ i, j ≤ d_ρ}` of the Fourier basis: pairs `(i, j)` of
basis indices of the same irrep (`ρ` is their common label). -/
def Idx (F : FourierData A Λ J) : Type w :=
  {p : J × J // F.lab p.1 = F.lab p.2}

/-- The row index `i` of `(ρ, i, j)`. -/
def Idx.row {F : FourierData A Λ J} (p : F.Idx) : J := (Subtype.val p).1

/-- The column index `j` of `(ρ, i, j)`. -/
def Idx.col {F : FourierData A Λ J} (p : F.Idx) : J := (Subtype.val p).2

instance (F : FourierData A Λ J) : Finite F.Idx :=
  inferInstanceAs (Finite {p : J × J // F.lab p.1 = F.lab p.2})

noncomputable instance (F : FourierData A Λ J) : Fintype F.Idx := Fintype.ofFinite _

instance (F : FourierData A Λ J) : DecidableEq F.Idx :=
  inferInstanceAs (DecidableEq {p : J × J // F.lab p.1 = F.lab p.2})

/-- A matrix unit inside one block is block diagonal. -/
theorem single_block (F : FourierData A Λ J) {i j : J} (h : F.lab i = F.lab j) :
    ∀ k l : J, F.lab k ≠ F.lab l → (Matrix.single i j (1 : ℂ)) k l = 0 := by
  intro k l hkl
  apply Matrix.single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact hkl h

/-- Definition 2.5 (PDF p. 15): the Fourier basis element `E^ρ_{ij}`, the preimage of the matrix
unit `|i⟩⟨j|_ρ` under the Fourier isomorphism. It is defined for basis indices `i, j` of the
same irrep (`lab i = lab j = ρ`); for indices of different irreps the value is `0`. -/
noncomputable def E (F : FourierData A Λ J) (i j : J) : A :=
  haveI : Decidable (F.lab i = F.lab j) := Classical.propDecidable _
  if h : F.lab i = F.lab j then
    Classical.choose (F.rep_surjective (Matrix.single i j (1 : ℂ)) (F.single_block h))
  else 0

theorem rep_E (F : FourierData A Λ J) {i j : J} (h : F.lab i = F.lab j) :
    F.rep (F.E i j) = Matrix.single i j (1 : ℂ) := by
  unfold E
  simp only [dif_pos h]
  exact Classical.choose_spec (F.rep_surjective (Matrix.single i j (1 : ℂ)) (F.single_block h))

/-- `E^ρ_{ij}` for a Fourier index `p = (ρ, i, j)`. -/
noncomputable def EI (F : FourierData A Λ J) (p : F.Idx) : A := F.E p.row p.col

end FourierData

/-- PDF p. 15, Eq. (2.3): the left regular trace form `τ_L(a) = Tr(L(a))`, the trace of left
multiplication by `a` on `A`. (For `A` not finite-dimensional over `ℂ` the value is `0`.) -/
noncomputable def regTrace (A : Type u) [Ring A] [Algebra ℂ A] (a : A) : ℂ :=
  LinearMap.trace ℂ A (LinearMap.mulLeft ℂ a)

/-- Definition 2.8 (PDF p. 15) for `τ = τ_L`: the family `bs = (a*)_{a}` is dual to the family
`b` with respect to the bilinear form `⟨x, y⟩_L = τ_L(x y)`, i.e. `⟨a_i*, a_j⟩_L = δ_{ij}`. -/
def IsRegDual {A : Type u} [Ring A] [Algebra ℂ A] {ι : Type x} [DecidableEq ι]
    (b bs : ι → A) : Prop :=
  ∀ i j : ι, regTrace A (bs i * b j) = if i = j then 1 else 0

/-- The computational basis `𝓑(A)` of Section 2.2, as used on a quantum computer: the basis
vectors `vec a` (`a ∈ ι`) and the linear map `coord` sending an element of `A` to its vector of
coordinates in `ℂ^ι`. No relation between the two is part of the structure; in every use
`coord (vec a)` is the `a`-th standard basis vector. -/
structure CompBasis (A : Type u) [Ring A] [Algebra ℂ A] (ι : Type x) where
  /-- The basis vectors. -/
  vec : ι → A
  /-- The coordinates of an element. -/
  coord : A →ₗ[ℂ] (ι → ℂ)

namespace CompBasis

variable {A : Type u} [Ring A] [Algebra ℂ A] {ι : Type x}

/-- The computational basis attached to a basis `b` of `A`: `vec = b`, and `coord x` is the
coordinate vector of `x` in the basis `b`. -/
noncomputable def ofBasis [Finite ι] (b : Module.Basis ι ℂ A) : CompBasis A ι where
  vec := b
  coord := b.equivFun.toLinearMap

/-- Definition 2.10 (PDF p. 16): the computational inner product
`⟨x, y⟩₀ = Σ_a conj(α_a) β_a` for `x = Σ α_a a`, `y = Σ β_a a`. -/
noncomputable def inner [Fintype ι] (c : CompBasis A ι) (x y : A) : ℂ :=
  ∑ a : ι, conj (c.coord x a) * c.coord y a

/-- PDF p. 18, Eq. (3.2): `‖x‖₂ = √⟨x, x⟩₀ = (Σ_a |α_a|²)^{1/2}`. -/
noncomputable def norm [Fintype ι] (c : CompBasis A ι) (x : A) : ℝ :=
  Real.sqrt (∑ a : ι, ‖c.coord x a‖ ^ 2)

end CompBasis

namespace FourierData

variable {A : Type u} [Ring A] [Algebra ℂ A] {Λ : Type v} {J : Type w}
  [Fintype J] [DecidableEq J] {ι : Type x} [Fintype ι]

/-- Definition 3.1 (PDF p. 18, Eq. (3.4)): the (normalized) Fourier transform
`FT_A |a⟩ = Σ_{ρ,i,j} (1/‖E^ρ_{ij}‖₂) ⟨E^ρ_{ij}, a⟩₀ |ρ, i, j⟩`, as the matrix with rows
`(ρ, i, j)` and columns `a ∈ 𝓑(A)`. -/
noncomputable def FT (F : FourierData A Λ J) (c : CompBasis A ι) : Matrix F.Idx ι ℂ :=
  Matrix.of fun p a => c.inner (F.EI p) (c.vec a) / (c.norm (F.EI p) : ℂ)

/-- Theorem 3.4 (PDF p. 20, Eq. (3.19)):
`F̃T_A |a⟩ = Σ_{ρ,i,j} ‖E^ρ_{ij}‖₂ · ρ(a)_{ij} |ρ, i, j⟩`. -/
noncomputable def FTtilde (F : FourierData A Λ J) (c : CompBasis A ι) : Matrix F.Idx ι ℂ :=
  Matrix.of fun p a => (c.norm (F.EI p) : ℂ) * F.rep (c.vec a) p.row p.col

/-- Definition 3.3 (PDF p. 20, Eq. (3.18)): the Gram matrix of the normalized Fourier basis with
respect to `⟨·,·⟩₀`,
`G_{(ρ,i,j),(σ,k,l)} = ⟨E^ρ_{ij}, E^σ_{kl}⟩₀ / (‖E^ρ_{ij}‖₂ ‖E^σ_{kl}‖₂)`. -/
noncomputable def gram (F : FourierData A Λ J) (c : CompBasis A ι) : Matrix F.Idx F.Idx ℂ :=
  Matrix.of fun p q => c.inner (F.EI p) (F.EI q) / ((c.norm (F.EI p) : ℂ) * (c.norm (F.EI q) : ℂ))

/-- Definition 3.3 (PDF p. 20): `A` is `δ`-nice (with respect to the computational basis and the
chosen Fourier basis) if `‖G - I‖_∞ ≤ δ`. -/
def IsNice (F : FourierData A Λ J) (c : CompBasis A ι) (δ : ℝ) : Prop :=
  QAlgorithms.specNorm (F.gram c - 1) ≤ δ

end FourierData

/-- Section 5.2 (PDF p. 32, Eqs. (5.7)–(5.8)): for semisimple subalgebras `B ⊆ A` of `R`, the
Fourier basis `FA` of `A` is `B`-adapted, with multiplicity-free branching, relative to the
Fourier basis `FB` of `B`. The map `tr` sends the basis index `k ∘ ρ` of an irrep `ρ` of `A`
(`k` a basis index of an irrep `σ ∈ Res(ρ)` of `B`) to `k`.

* `rep_eq`, `rep_zero`: for `b ∈ B`, the block `ρ(b)` is the direct sum of the blocks `σ(b)`,
  `σ ∈ Res(ρ)`: `ρ(b)_{k∘ρ, l∘ρ} = σ(b)_{kl}` when `k`, `l` belong to the same irrep `σ` of `B`,
  and the entry is `0` when they belong to different irreps of `B`.
* `tr_injective`, `tr_full`: within one irrep `ρ` of `A`, `tr` is a bijection from the basis
  indices of `ρ` onto the union of the full index sets of the irreps `σ ∈ Res(ρ)`, each
  occurring once (multiplicity-free). -/
structure IsAdapted {R : Type u} [Ring R] [Algebra ℂ R] {A B : Subalgebra ℂ R} (hBA : B ≤ A)
    {ΛA : Type*} {JA : Type*} [Fintype JA] [DecidableEq JA]
    {ΛB : Type*} {JB : Type*} [Fintype JB] [DecidableEq JB]
    (FA : FourierData A ΛA JA) (FB : FourierData B ΛB JB) (tr : JA → JB) : Prop where
  rep_eq : ∀ (b : R) (hb : b ∈ B) (P Q : JA), FA.lab P = FA.lab Q →
    FB.lab (tr P) = FB.lab (tr Q) → FA.rep ⟨b, hBA hb⟩ P Q = FB.rep ⟨b, hb⟩ (tr P) (tr Q)
  rep_zero : ∀ (b : R) (hb : b ∈ B) (P Q : JA), FA.lab P = FA.lab Q →
    FB.lab (tr P) ≠ FB.lab (tr Q) → FA.rep ⟨b, hBA hb⟩ P Q = 0
  tr_injective : ∀ P Q : JA, FA.lab P = FA.lab Q → tr P = tr Q → P = Q
  tr_full : ∀ (P : JA) (k : JB), FB.lab k = FB.lab (tr P) →
    ∃ Q : JA, FA.lab Q = FA.lab P ∧ tr Q = k

end SemisimpleQFT


