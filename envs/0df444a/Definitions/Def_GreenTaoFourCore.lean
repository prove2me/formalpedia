-- Prove2me | Definitions.Def_GreenTaoFourCore
-- name    : GreenTaoFourCore
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-28T10:29:14.92886+00:00
-- url     : https://prove2.me/theorems/623b1e10-6bdc-459b-bb74-a0e6019e4d60
-- title:
--   Core objects of Green–Tao's polylogarithmic bound for $r_4(N)$
-- statement:
--   This definition bundle collects the objects used in the formalized proof of the Green–Tao bound $r_4(N)\ll N(\log N)^{-c}$:
--
--   1. Circle distance $\|x/N\|_{\mathbb{R}/\mathbb{Z}}$, Bohr sets $B(\Gamma,\rho)=\{x:\|\gamma x/N\|\le\rho\ \forall\gamma\in\Gamma\}$, the dual norm $\|h\|_{S^\perp}$, uniform measures $\mu_B$ and the regular distributions $P_{S,\rho}(a)=2\int_{1/2}^1\mu_{B(S,t\rho)}(a)\,dt$.
--   2. Characters $e(x)$ on $\mathbb{R}/\mathbb{Z}$ and $e_N(x)$ on $\mathbb{Z}/N\mathbb{Z}$; additivity on a Bohr scale; locally quadratic maps (vanishing third differences on cubes in a set).
--   3. Tori $G=\mathbb{R}^d/\Lambda$ given by a lattice basis $v_1,\dots,v_d\in\mathbb{R}^n$, Lipschitz functions on them, their volume and non-degeneracy.
--   4. Structured local approximants (Definition 6.1), their random triples $(\mathbf a,\mathbf r,\mathbf f)$, energy, edges (Definition 6.3), the bounds (6.4)–(6.7), and the refinement of poorly distributed labels.
--   5. The quantities appearing in the local inverse $U^3$ theorem (Theorem 8.1) and its proof (quadruple averages, penalised weights, local $U^2$ averages, densities $\alpha_i$), and the explicit constants $C_2<C_3<C_4<C_5$ and parameter functions of the argument.
--
--   **Formalization Note.** The bundle only contains definitions (and a handful of trivial structural lemmas needed to state them); all theorems are published separately as children of `Erdos142.green_tao_four`.
-- source:
--   B. Green and T. Tao, New bounds for Szemerédi's theorem, III: a polylogarithmic bound for r_4(N), Mathematika 63 (2017), https://arxiv.org/abs/1705.01703, Sections 4-9

import Mathlib

section Def_KM_Bohr
/-!
# Bohr sets in `ZMod N`

We define the circle distance `cn`, Bohr sets `bohr Γ ρ`, prove the basic covering bound
`|bohr Γ ρ| ≤ (4ρ/ρ')^d |bohr Γ ρ'|`, the absolute lower bound `|bohr Γ ρ| ≥ N (ρ/2)^d`, and the
existence of regular radii.
-/

open Finset

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The distance from `z / N` to the nearest integer. -/
def cn (z : ZMod N) : ℝ := ‖ZMod.toAddCircle z‖

/-- The Bohr set with frequency set `Γ` and radius `ρ`. -/
def bohr (Γ : Finset (ZMod N)) (ρ : ℝ) : Finset (ZMod N) :=
  univ.filter fun x => ∀ γ ∈ Γ, cn (γ * x) ≤ ρ

variable {Γ Γ' : Finset (ZMod N)} {ρ ρ' : ℝ} {x y : ZMod N}

/-! ### The covering bound -/

/-! ### Regularity -/

/-! ### Dilation by a unit -/

end

end KM
end Def_KM_Bohr

section Def_KM_Conv
/-!
# Convolutions and normalised indicator functions on a finite abelian group
-/

open Finset

namespace KM

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Uniform probability measure on a finset. -/
def mu (S : Finset G) : G → ℝ := fun x => if x ∈ S then (S.card : ℝ)⁻¹ else 0

variable {S T A B : Finset G} {f g h : G → ℝ} {x y t : G}

/-! ### Reindexing -/

/-! ### Basic properties of convolutions -/

/-! ### Translates of indicator functions -/

end

end KM
end Def_KM_Conv

section Def_GT_Bohr
/-!
# Regular probability distributions on Bohr sets (Green–Tao §4)

`regP Γ ρ a = 2 ∫_{1/2}^1 μ_{B(Γ, tρ)}(a) dt`, and the approximate translation invariance
(Lemma 4.4): translating by an element of `B(Γ', ρ')`, `Γ ⊆ Γ'`, changes `regP Γ ρ` by at most
`O(|Γ| ρ'/ρ)` in total variation.
-/

open Finset MeasureTheory KM

namespace GT

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The regular probability distribution on the Bohr set `B(Γ, ρ)`. -/
def regP (Γ : Finset (ZMod N)) (ρ : ℝ) (a : ZMod N) : ℝ :=
  2 * ∫ t in (1 / 2 : ℝ)..1, mu (bohr Γ (t * ρ)) a

variable (Γ : Finset (ZMod N)) {ρ : ℝ}

end

end GT
end Def_GT_Bohr

section Def_KM_Fourier
/-!
# Fourier analysis on `ZMod N`
-/

open Finset
open ComplexConjugate

namespace KM

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The character `x ↦ e(x/N)`. -/
def ech (z : ZMod N) : ℂ := ZMod.stdAddChar z

end

end KM
end Def_KM_Fourier

section Def_GT_Prob
/-!
# Common toolkit for the Green–Tao argument

* the exponential `e(x)` of a point of `ℝ/ℤ`, with the bounds `4‖x‖ ≤ |e(x) - 1| ≤ 2π‖x‖`;
* the dual norm `‖h‖_{S^⊥}` (`snorm`) and its relation with Bohr sets;
* support and translation properties of the regular distributions `regP`;
* the local inverse `U²` theorem for regular distributions on Bohr sets.
-/

open Finset ComplexConjugate KM

namespace GT

noncomputable section

/-! ### The exponential on `ℝ/ℤ` -/

/-- `e(x) = exp(2πi x)` for `x ∈ ℝ/ℤ`. -/
def ec (x : UnitAddCircle) : ℂ := ((AddCircle.toCircle x : Circle) : ℂ)

variable {N : ℕ} [NeZero N]

/-! ### The dual norm `‖h‖_{S^⊥}` -/

/-- `‖h‖_{S^⊥} = max_{s ∈ S} ‖s h / N‖_{ℝ/ℤ}` (zero if `S` is empty). -/
def snorm (S : Finset (ZMod N)) (h : ZMod N) : ℝ :=
  if hS : S.Nonempty then S.sup' hS fun s => cn (s * h) else 0

variable {S : Finset (ZMod N)}

/-! ### Regular distributions -/

/-! ### Averages against probability vectors -/

section avg

variable {α : Type*} [Fintype α] {P : α → ℝ}

end avg

end

end GT
end Def_GT_Prob

section Def_GT_AddOn
/-!
# Local additivity on Bohr sets

`AddOn S R f` says that `f (x + y) = f x + f y` whenever `‖x‖_{S^⊥} + ‖y‖_{S^⊥} ≤ R`.
Locally linear maps on Bohr sets (and the partial maps of locally bilinear maps) are of this
form; we record how they act on integer combinations.
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

/-- Additivity under an `S^⊥`-norm budget `R`. -/
def AddOn (S : Finset (ZMod p)) (R : ℝ) (f : ZMod p → M) : Prop :=
  ∀ x y, snorm S x + snorm S y ≤ R → f (x + y) = f x + f y

namespace AddOn

variable {R : ℝ} {f : ZMod p → M}

end AddOn

end

end GT
end Def_GT_AddOn

section Def_GT_Lattice
/-!
# Gram determinants and reduced lattice bases

Toolkit for lattices `⊕ ℤ v_i` in a real inner product space:
* the Gram determinant transforms by `det(M)^2` under a change of family `v ↦ M v`;
* orthogonal splitting `det Gram(x, w) = ‖x‖² det Gram(w)` when `x ⊥ w`;
* Hadamard's inequality `det Gram(v) ≤ ∏ ‖v_i‖²`;
* the coordinate bound `|t_i| √det Gram(v) ≤ ‖∑ t_j v_j‖ ∏_{j ≠ i} ‖v_j‖`;
* completion of a primitive integer vector to a unimodular matrix;
* Hermite reduction: every lattice has a basis with `(∏‖b_i‖)² ≤ 2^{r²} det Gram`.
-/

open Finset Matrix

namespace GT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant. -/
abbrev gdet {r : ℕ} (v : Fin r → E) : ℝ := (Matrix.gram ℝ v).det

end

end GT
end Def_GT_Lattice

section Def_GT_Torus
/-!
# Tori and locally quadratic maps (Green–Tao §4, §5)

Green–Tao work with *dilated tori* `∏ ℝ/λ_i ℤ`.  Since the orthogonal complement of a dual
frequency in a dilated torus is not itself a dilated torus (their Theorem 5.1 handles this by a
bilipschitz reparametrisation), we instead work with the slightly more general class of tori
`ℝ^d / Γ`, where `Γ` is a lattice with a given basis, isometrically embedded in a Euclidean
space.  Concretely a torus `G` is given by vectors `v_1, …, v_d` of `ℝ^n`; its points are
`(ℝ/ℤ)^d`, the point with coordinates `t` corresponds to `∑ t_i v_i` modulo the lattice
`Γ = ⊕ ℤ v_i`, and the metric is the quotient Euclidean metric.  The volume is the covolume of
`Γ`, i.e. the square root of the Gram determinant of the `v_i`.  Dilated tori are the case of
orthogonal `v_i` with `‖v_i‖ = λ_i`.
-/

namespace GT

noncomputable section

open Finset

/-- A torus `ℝ^d / (⊕ ℤ v_i)`, with the lattice embedded in `ℝ^n`. -/
structure DTorus where
  d : ℕ
  n : ℕ
  v : Fin d → EuclideanSpace ℝ (Fin n)

namespace DTorus

/-- Points of the torus, in coordinates `(ℝ/ℤ)^d`. -/
abbrev Pt (G : DTorus) : Type := Fin G.d → UnitAddCircle

/-- The embedding of coordinates `t ∈ ℝ^d` into `ℝ^n`: `t ↦ ∑ t_i v_i`. -/
def emb (G : DTorus) (t : Fin G.d → ℝ) : EuclideanSpace ℝ (Fin G.n) := ∑ i, t i • G.v i

/-- The point of the torus with real coordinates `t`. -/
def pt (G : DTorus) (t : Fin G.d → ℝ) : G.Pt := fun i => (t i : UnitAddCircle)

/-- `F` is `1`-Lipschitz for the quotient Euclidean metric. -/
def IsLip (G : DTorus) (F : G.Pt → ℝ) : Prop :=
  ∀ t t' : Fin G.d → ℝ, |F (G.pt t) - F (G.pt t')| ≤ ‖G.emb (t - t')‖

/-- The volume `∏ ‖v_i‖`; for a reduced basis this is comparable to the covolume. -/
def vol (G : DTorus) : ℝ := ∏ i, ‖G.v i‖

/-- Non-degeneracy: the `v_i` are linearly independent, the lattice has no non-zero vector
of length `< 1`, and the basis is (Hermite-)reduced: `(∏ ‖v_i‖)² ≤ 2^{d²} det Gram(v)`. -/
def Good (G : DTorus) : Prop :=
  LinearIndependent ℝ G.v ∧ (∀ m : Fin G.d → ℤ, m ≠ 0 → 1 ≤ ‖G.emb (fun i => (m i : ℝ))‖) ∧
    (∏ i, ‖G.v i‖) ^ 2 ≤ 2 ^ (G.d ^ 2) * gdet G.v

/-- The zero-dimensional torus (a point). -/
def point : DTorus := ⟨0, 0, Fin.elim0⟩

instance : IsEmpty (Fin point.d) := (Fin.isEmpty' : IsEmpty (Fin 0))

end DTorus

/-- `Ξ` is locally quadratic on `B`: its third differences vanish on cubes inside `B`. -/
def LocQuad {p : ℕ} {M : Type*} [AddCommGroup M] (B : Set (ZMod p)) (Ξ : ZMod p → M) : Prop :=
  ∀ n h₁ h₂ h₃ : ZMod p, n ∈ B → n + h₁ ∈ B → n + h₂ ∈ B → n + h₃ ∈ B → n + h₁ + h₂ ∈ B →
    n + h₁ + h₃ ∈ B → n + h₂ + h₃ ∈ B → n + h₁ + h₂ + h₃ ∈ B →
    Ξ (n + h₁ + h₂ + h₃) - Ξ (n + h₁ + h₂) - Ξ (n + h₁ + h₃) - Ξ (n + h₂ + h₃)
      + Ξ (n + h₁) + Ξ (n + h₂) + Ξ (n + h₃) - Ξ n = 0

end

end GT
end Def_GT_Torus

section Def_GT_LocQ
/-!
# Calculus of locally quadratic maps on shifted Bohr sets

For `Ξ` locally quadratic on `n₀ + B(S, ρ)` we study the second difference
`D2 Ξ a h k = Ξ(a+h+k) - Ξ(a+h) - Ξ(a+k) + Ξ(a)`: it does not depend on the base point and is
additive in each variable (under `S^⊥`-norm budgets).
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p] {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M]

/-- The shifted Bohr set `n₀ + B(S, ρ)`. -/
def sBohr (S : Finset (ZMod p)) (n0 : ZMod p) (ρ : ℝ) : Set (ZMod p) :=
  {x | x - n0 ∈ bohr S ρ}

/-- The second difference. -/
def D2 (Ξ : ZMod p → M) (a h k : ZMod p) : M := Ξ (a + h + k) - Ξ (a + h) - Ξ (a + k) + Ξ a

variable {n0 : ZMod p} {ρ : ℝ} {Ξ : ZMod p → M}

end

end GT
end Def_GT_LocQ

section Def_GT_InvU3
/-!
# The local inverse `U³` theorem (Green–Tao, Theorem 8.1)

We use one geometric sequence of scales `θ^t ρ₀`.  The `U³` hypothesis is taken with the
variables `h₀, h₁, h₂` drawn regularly from `B(S, ρ₀)`, `B(S, θρ₀)`, `B(S, θ²ρ₀)`; the
conclusion is a correlation of `f(n + k m)` with a locally quadratic phase in `m` plus a linear
phase `β(n) m / p`, with `n` drawn from `B(S, ρ₀)` and `m` from `B(S', θ^T ρ₀)`.
-/

open Finset KM ComplexConjugate

namespace GT

noncomputable section

/-- The exponent controlling the rank increase and the depth. -/
def u3EJ : ℕ := 2 ^ 24

/-- The final correlation `κ(η)`. -/
def u3κ (η : ℝ) : ℝ := η ^ (2 ^ 20)

/-- The bound on the rank increase. -/
def u3J (η : ℝ) : ℝ := (1 / η) ^ u3EJ

/-- The depth `T(η)`: the final scale is `θ^T ρ₀`. -/
def u3T (η : ℝ) : ℕ := 20 * ⌊u3J η⌋₊ + 100

/-- The bound on the dilation factor `k`. -/
def u3k (s : ℕ) (η : ℝ) : ℝ := Real.exp ((s + u3J η + 1) ^ 3)

/-- The smallness required of the scale ratio `θ`. -/
def u3θ (s : ℕ) (η : ℝ) : ℝ := Real.exp (-(s + u3J η + 1) ^ 4)

/-- The largeness required of `p`. -/
def u3P (s : ℕ) (η θ ρ0 : ℝ) : ℝ :=
  (4 / (θ ^ u3T η * ρ0)) ^ (4 * (s + ⌊u3J η⌋₊ + 1)) * (1 / η) ^ (2 ^ 30)

/-- The `U³`-type average of Theorem 8.1 at scales `ρ₀, ρ₁, ρ₂`. -/
def u3avg {p : ℕ} [NeZero p] (S : Finset (ZMod p)) (ρ0 ρ1 ρ2 : ℝ) (f : ZMod p → ℂ) : ℂ :=
  ∑ h0, ∑ h0', ∑ h1, ∑ h1', ∑ h2, ∑ h2',
    ((regP S ρ0 h0 * regP S ρ0 h0' * regP S ρ1 h1 * regP S ρ1 h1' * regP S ρ2 h2 *
      regP S ρ2 h2' : ℝ) : ℂ) *
    (f (h0 + h1 + h2) * conj (f (h0 + h1' + h2)) * conj (f (h0' + h1 + h2)) *
      f (h0' + h1' + h2) * conj (f (h0 + h1 + h2')) * f (h0 + h1' + h2') *
      f (h0' + h1 + h2') * conj (f (h0' + h1' + h2')))

/- The local inverse `U³` theorem itself, `GT.inv_u3`, is proved in `RequestProject.GT.InvU3Thm`. -/

end

end GT
end Def_GT_InvU3

section Def_GT_Unimod
/-!
# Completing a primitive integer vector to a unimodular matrix
-/

open Matrix

namespace GT

/-- An integer vector is primitive if the gcd of its entries is `1`. -/
def Prim {ι : Type*} (m : ι → ℤ) : Prop := ∀ q : ℤ, (∀ j, q ∣ m j) → IsUnit q

end GT
end Def_GT_Unimod

section Def_GT_Hermite
/-!
# Hermite reduction of lattice bases

Every lattice `⊕ ℤ u_i` (with `u` linearly independent) has a basis `b = M u`, `M ∈ GL_r(ℤ)`,
with `(∏ ‖b_i‖)² ≤ 2^{r²} det Gram(u)`.
-/

open Finset Matrix

namespace GT

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The lattice vector with integer coordinates `m`. -/
def zvec {r : ℕ} (m : Fin r → ℤ) (u : Fin r → E) : E := ∑ j, (m j : ℝ) • u j

/-- The family `M u` for an integer matrix `M`. -/
def zmix {r s : ℕ} (M : Matrix (Fin r) (Fin s) ℤ) (u : Fin s → E) : Fin r → E :=
  fun i => zvec (M i) u

end

end GT
end Def_GT_Hermite

section Def_GT_LargeQuad
/-!
# Large local quadratic exponential sums (Green–Tao, Proposition 4.9)
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The radius `τ = δρ/(200 d)` of the shifts in Proposition 4.9. -/
def lqτ (d : ℕ) (δ ρ : ℝ) : ℝ := δ * ρ / (200 * d)

/-- The radius on which Proposition 4.9 gives control. -/
def lqR (d : ℕ) (δ ρ : ℝ) : ℝ := lqτ d δ ρ / (2 ^ (d ^ 2) * d * (65536 / δ ^ 3 + 1))

/-- The constant in the conclusion of Proposition 4.9. -/
def lqK (d : ℕ) (δ ρ : ℝ) : ℝ :=
  d ^ 2 * (2 * (2 ^ (d ^ 2) * d) / lqτ d δ ρ) ^ 2 * (32 / δ) ^ (d ^ 2) * (131072 / δ ^ 4)

end

end GT
end Def_GT_LargeQuad

section Def_GT_WeylStep
/-!
# The Weyl step of Proposition 7.1 (Green–Tao, Lemmas 3.2 and 7.2)

A poorly distributed label produces a non-zero frequency `k = (k₀, k₁, k₂)` with coordinates
`|k_{j,i}| ≲ (d/η)‖v_i‖` such that `E e(k₀·Ξ(a) + k₁·Ξ(a+r) + k₂·Ξ(a+2r))` is large.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

/-- The pairing `k · x = ∑ kᵢ xᵢ ∈ ℝ/ℤ`, as an additive homomorphism in `x`. -/
def kdot {ι : Type*} [Fintype ι] (k : ι → ℤ) : (ι → UnitAddCircle) →+ UnitAddCircle where
  toFun x := ∑ i, k i • x i
  map_zero' := by simp
  map_add' x y := by simp [smul_add, sum_add_distrib]

namespace DTorus

end DTorus

/-- The Weyl cut-off `M_i = ⌈1000 (d+1) ‖v_i‖ / η⌉`. -/
def wM (G : DTorus) (η : ℝ) (i : Fin G.d) : ℕ := ⌈1000 * (G.d + 1) / η * ‖G.v i‖⌉₊

end

end GT
end Def_GT_WeylStep

section Def_GT_Subtorus
/-!
# Subtori of lattice tori (replacement for Green–Tao, Theorem 5.1)

For a primitive frequency `k ∈ ℤ^d` of a lattice torus `G`, the subtorus `k^⊥` is again a
lattice torus `G.sub B` (with basis given by an integer matrix `B`), and there is a projection
`π` with `y = ι(π y) + (k·y) u` for a fixed integer vector `u` with `k·u = 1`.
-/

open Finset Matrix

namespace GT

noncomputable section

/-- The homomorphism `(ℝ/ℤ)^b → (ℝ/ℤ)^a` induced by an integer matrix. -/
def zmap {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℤ) :
    (Fin b → UnitAddCircle) →+ (Fin a → UnitAddCircle) where
  toFun x j := ∑ i, M j i • x i
  map_zero' := by funext j; simp
  map_add' x y := by funext j; simp [smul_add, sum_add_distrib]

namespace DTorus

/-- The lattice torus spanned by the integer combinations `B` of the basis of `G`. -/
abbrev sub (G : DTorus) {d' : ℕ} (B : Matrix (Fin d') (Fin G.d) ℤ) : DTorus :=
  ⟨d', G.n, zmix B G.v⟩

end DTorus

section lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end lattice

end

end GT
end Def_GT_Subtorus

section Def_GT_Prop71
/-!
# Proposition 7.1 of Green–Tao

A poorly distributed label gives a primitive dual frequency `k'`, a multiplier `m`, and for each
base point `a` of the Bohr set a frequency `ξ_a`, such that `k'·(Ξ(a + 2mh) − Ξ(a))` is small
for `h` in a small Bohr set with frequencies `S ∪ {ξ_a}`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

variable {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M] {n0 : ZMod p} {ρ : ℝ}
  {Ξ : ZMod p → M}

/-- The product of the Weyl cut-offs. -/
def wP (G : DTorus) (η : ℝ) : ℝ := (∏ i, (2 * wM G η i : ℝ)) ^ 3

/-- The correlation `δ = η / (256 P)` produced by the Weyl step. -/
def wδ (G : DTorus) (η : ℝ) : ℝ := η / (256 * wP G η)

/-- The scale of the differencing variable `h` in the Weyl differencing. -/
def wρh (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) : ℝ :=
  wδ G η * ε4 * ρ / (1000 * (S.card + 1))

/-- The correlation parameter entering the Weyl differencing tail. -/
def p71δ (G : DTorus) (η : ℝ) : ℝ := wδ G η / 4

/-- The radius on which the bilinear bound holds. -/
def p71R (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) : ℝ :=
  lqR S.card (p71δ G η ^ 4) (wρh S G η ε4 ρ)

/-- The constant of the bilinear bound. -/
def p71K (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) : ℝ :=
  lqK S.card (p71δ G η ^ 4) (wρh S G η ε4 ρ)

/-- The constant `A` fed to Corollary 4.11. -/
def p71A (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) : ℝ :=
  p71K S G η ε4 ρ * (2 * p71R S G η ε4 ρ) ^ 2 + 1

/-- The Lipschitz constant produced by Corollary 4.11. -/
def p71E (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) : ℝ :=
  10 ^ 9 * √(p71A S G η ε4 ρ) * (S.card : ℝ) ^ 4 / (2 * p71R S G η ε4 ρ)

/-- The bound on the multiplier `m`. -/
def p71m (S : Finset (ZMod p)) (G : DTorus) (η : ℝ) : ℝ :=
  (32 / p71δ G η ^ 4) ^ (S.card ^ 2) * (4 * ∑ i, (wM G η i : ℝ))

end

end GT
end Def_GT_Prop71

section Def_GT_Refine
/-!
# Refining a poorly distributed label

Combining Proposition 7.1 with the subtorus construction: a poorly distributed label admits a
codimension-one subtorus such that, near every base point, `F ∘ Ξ` is approximated by a function
on the subtorus.
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The Lipschitz constant in the conclusion of Proposition 7.1. -/
def p71L (S : Finset (ZMod p)) (G : DTorus) (η ε4 ρ : ℝ) (m : ℕ) : ℝ :=
  2 + 2 * p71E S G η ε4 ρ + 4 * m * p71K S G η ε4 ρ * p71R S G η ε4 ρ

end

end GT
end Def_GT_Refine

section Def_GT_Iter
/-!
# The energy/dimension iteration (Green–Tao, end of §3)

A *random triple* `(a, r, 𝐟)` in which `𝐟` becomes deterministic after conditioning on a
finite label `c` is encoded by `Triple p`: a finite label type with a probability vector `π`,
for each label a joint law `w c` of `(a, r)`, and a function `F c`.

`MainAbstract C₂ C₅` is Proposition 3.3 of Green–Tao (with the path-length bound `64 η^{-2C₂}`
and the thickness bound `exp(η^{-C₅})/p`), and `khint_of_mainAbstract` deduces Theorem 3.1.
-/

open Finset

namespace GT

noncomputable section

/-- A random triple `(a, r, 𝐟)` with `𝐟` deterministic given a finite label. -/
structure Triple (p : ℕ) where
  L : Type
  [fL : Fintype L]
  π : L → ℝ
  w : L → ZMod p × ZMod p → ℝ
  F : L → ZMod p → ℝ

attribute [instance] Triple.fL

namespace Triple

variable {p : ℕ} [NeZero p] (t : Triple p) (f : ZMod p → ℝ)

/-- `E g(a)` for a deterministic `g`. -/
def ex (g : ZMod p → ℝ) : ℝ := ∑ c, t.π c * ∑ z, t.w c z * g z.1

/-- `E 𝐟(a)`. -/
def exF : ℝ := ∑ c, t.π c * ∑ z, t.w c z * t.F c z.1

/-- `Λ_{a,r}(g)` for a deterministic `g`. -/
def lam (g : ZMod p → ℝ) : ℝ :=
  ∑ c, t.π c * ∑ z, t.w c z * (g z.1 * g (z.1 + z.2) * g (z.1 + 2 * z.2) * g (z.1 + 3 * z.2))

/-- `Λ_{a,r}(𝐟)`. -/
def lamF : ℝ :=
  ∑ c, t.π c * ∑ z, t.w c z *
    (t.F c z.1 * t.F c (z.1 + z.2) * t.F c (z.1 + 2 * z.2) * t.F c (z.1 + 3 * z.2))

/-- The energy `E |f(a) - 𝐟(a)|^2`. -/
def energy : ℝ := ∑ c, t.π c * ∑ z, t.w c z * (f z.1 - t.F c z.1) ^ 2

end Triple

namespace Triple

variable {p : ℕ} [NeZero p] {t : Triple p} {f : ZMod p → ℝ}

end Triple

end

end GT
end Def_GT_Iter

section Def_GT_SLA
/-!
# Structured local approximants (Green–Tao, Definition 6.1)
-/

open Finset KM

namespace GT

noncomputable section

/-- The constants `C₂ < C₃ < C₄ < C₅` of Green–Tao (each large in terms of the previous). -/
def C2 : ℕ := 2 ^ 32
def C3 : ℕ := 2 ^ 64
def C4 : ℕ := 2 ^ 256
def C5 : ℕ := 2 ^ 1024

/-- A structured local approximant (Definition 6.1). -/
structure SLA (p : ℕ) where
  C : Type
  [fC : Fintype C]
  prob : C → ℝ
  n : C → ZMod p
  S : C → Finset (ZMod p)
  ρ : C → ℝ
  G : C → DTorus
  F : (c : C) → (G c).Pt → ℝ
  Ξ : (c : C) → ZMod p → (G c).Pt

attribute [instance] SLA.fC

namespace SLA

variable {p : ℕ} [NeZero p] (v : SLA p) (η : ℝ) (f : ZMod p → ℝ)

/-- The shifted Bohr set `n_c + B(S_c, ρ_c)`. -/
def shB (c : v.C) : Set (ZMod p) := {x | x - v.n c ∈ bohr (v.S c) (v.ρ c)}

/-- Validity of a structured local approximant. -/
def Valid : Prop :=
  (∀ c, 0 ≤ v.prob c) ∧ ∑ c, v.prob c = 1 ∧ (∀ c, ∃ s ∈ v.S c, s ≠ 0) ∧
    (∀ c, 0 < v.ρ c ∧ v.ρ c ≤ 1) ∧ (∀ c, (v.G c).IsLip (v.F c)) ∧ (∀ c x, |v.F c x| ≤ 1) ∧
    (∀ c, LocQuad (v.shB c) (v.Ξ c)) ∧ ∀ c, (v.G c).Good

/-- The scale `exp(-η^{-C₄})` of the difference variable `r`. -/
def eps4 : ℝ := Real.exp (-(1 / η) ^ C4)

/-- The random triple `(a_v, r_v, 𝐟_v)`: given `c`, `a` is drawn regularly from
`n_c + B(S_c, ρ_c/2)`, `r` regularly from `B(S_c, exp(-η^{-C₄}) ρ_c)`, and `𝐟 = F_c ∘ Ξ_c`. -/
def triple : Triple p where
  L := v.C
  π := v.prob
  w c z := regP (v.S c) (v.ρ c / 2) (z.1 - v.n c) * regP (v.S c) (eps4 η * v.ρ c) z.2
  F c a := v.F c (v.Ξ c a)

/-- The linear rank `d₁(v) = max_c |S_c|`. -/
def d1 : ℕ := univ.sup fun c => (v.S c).card

/-- The quadratic dimension `d₂(v) = max_c dim G_c`. -/
def d2 : ℕ := univ.sup fun c => (v.G c).d

/-- The linear scale `ρ(v) = min_c ρ_c`. -/
def rmin : ℝ := ⨅ c, v.ρ c

/-- The quadratic volume `vol(v) = max_c vol(G_c)`. -/
def volm : ℝ := ⨆ c, (v.G c).vol

/-- The waste `|E f(a) - E_x f(x)|`. -/
def waste : ℝ := |(v.triple η).ex f - ∑ x, f x / p|

/-- `Λ(𝐟 | c = c)`. -/
def condLam (c : v.C) : ℝ :=
  ∑ z, (v.triple η).w c z * ((v.triple η).F c z.1 * (v.triple η).F c (z.1 + z.2) *
    (v.triple η).F c (z.1 + 2 * z.2) * (v.triple η).F c (z.1 + 3 * z.2))

/-- `E(𝐟(a) | c = c)`. -/
def condEx (c : v.C) : ℝ := ∑ z, (v.triple η).w c z * (v.triple η).F c z.1

/-- `c` is poorly distributed. -/
def Poor (c : v.C) : Prop := v.prob c ≠ 0 ∧ v.condLam η c < v.condEx η c ^ 4 - η / 2

open Classical in
/-- The poorly distributed quadratic dimension. -/
def d2p : ℕ := (univ.filter fun c => v.Poor η c).sup fun c => (v.G c).d

/-- The edge relation of Definition 6.3. -/
def Edge (v' : SLA p) : Prop :=
  (v'.d1 : ℝ) ≤ v.d1 + (1 / η) ^ C2 ∧ v'.d2 ≤ v.d2 + 1 ∧
    Real.exp (-(1 / η) ^ C5) * v.rmin ≤ v'.rmin ∧
    v'.volm ≤ Real.exp ((1 / η) ^ C3) * v.volm ∧ |v.waste η f - v'.waste η f| ≤ η ^ C3

/-- The bounds (6.4)–(6.7) valid near the initial approximant. -/
def Bounds : Prop :=
  (v.d1 : ℝ) ≤ 65 * (1 / η) ^ (3 * C2) ∧ (v.d2 : ℝ) ≤ 64 * (1 / η) ^ (2 * C2) ∧
    Real.exp (-(1 / η) ^ (2 * C5)) ≤ v.rmin ∧ v.volm ≤ Real.exp ((1 / η) ^ (2 * C3))

end SLA

end

end GT
end Def_GT_SLA

section Def_GT_BadDimData
/-!
# Infrastructure for Theorem 6.7: label data, refined labels, averages
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The data attached to one label of a structured local approximant. -/
structure LData (p : ℕ) where
  n : ZMod p
  S : Finset (ZMod p)
  ρ : ℝ
  G : DTorus
  F : G.Pt → ℝ
  Ξ : ZMod p → G.Pt

/-- The data used to refine a poorly distributed label. -/
structure RData (p : ℕ) (G : DTorus) where
  m : ℕ
  ξ : ZMod p → ZMod p
  d' : ℕ
  B : Matrix (Fin d') (Fin G.d) ℤ
  π : (Fin G.d → UnitAddCircle) →+ (Fin d' → UnitAddCircle)
  u : Fin G.d → ℤ

namespace LData

/-- The refined label at base `a + t`. -/
def refine (L : LData p) (r : RData p L.G) (a t : ZMod p) (τ : ℝ) : LData p where
  n := a + t
  S := (insert (r.ξ a) L.S).image (fun s => s * ((2 * r.m : ℕ) : ZMod p)⁻¹)
  ρ := τ
  G := L.G.sub r.B
  F := fun y => L.F (zmap r.Bᵀ y + L.Ξ (a + t))
  Ξ := fun x => r.π (L.Ξ x - L.Ξ (a + t))

end LData

namespace SLA

/-- The data of a label. -/
def ldata (v : SLA p) (c : v.C) : LData p := ⟨v.n c, v.S c, v.ρ c, v.G c, v.F c, v.Ξ c⟩

/-- Assembling a structured local approximant from label data. -/
def ofData (C : Type) [Fintype C] (prob : C → ℝ) (D : C → LData p) : SLA p where
  C := C
  prob := prob
  n c := (D c).n
  S c := (D c).S
  ρ c := (D c).ρ
  G c := (D c).G
  F c := (D c).F
  Ξ c := (D c).Ξ

end SLA

/-! ### Locally quadratic maps -/

/-! ### Dilated frequency sets -/

end

end GT
end Def_GT_BadDimData

section Def_GT_BadDim
/-!
# Theorem 6.7: bad lower bound implies dimension decrement

The refined approximant: every label `c` is replaced by the labels `(c, a, t)`, where `a` is drawn
from `n_c + B(S_c, ρ_c/2)` and `t` from `B(S_c, σ_c)`. For a poorly distributed `c` the label
`(c, a, t)` gets centre `a + t`, the frequencies `(2m)^{-1}(S_c ∪ {ξ_a})`, a tiny radius `τ_c`
and the codimension one subtorus given by Proposition 7.1; otherwise the data of `c` are copied.
-/

open Finset KM Matrix

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

namespace LData

end LData

namespace SLA

variable (v : SLA p) (η : ℝ)

/-- The radius `σ_c` of the auxiliary shift `t`. -/
def sig (c : v.C) : ℝ := p71R (v.S c) (v.G c) η (eps4 η) (v.ρ c)

/-- The new radius `τ_c`. -/
def tau (c : v.C) : ℝ := v.ρ c * Real.exp (-(1 / η) ^ (2 * C4))

/-- The properties of the refinement data of a poorly distributed label (Prop. 7.1). -/
def RProp (c : v.C) (r : RData p (v.G c)) : Prop :=
  1 ≤ r.m ∧ (r.m : ℝ) ≤ p71m (v.S c) (v.G c) η ∧ r.d' + 1 = (v.G c).d ∧
    ((v.G c).sub r.B).Good ∧
    ((v.G c).sub r.B).vol ≤
      2 ^ ((v.G c).d ^ 2) * (∑ i, 4 * (wM (v.G c) η i : ℝ) / ‖(v.G c).v i‖) * (v.G c).vol ∧
    (∀ i, |(r.u i : ℝ)| ≤ 1 + ∑ j, 4 * (wM (v.G c) η j : ℝ)) ∧
    ∀ a, snorm (v.S c) (a - v.n c) ≤ v.ρ c / 2 → ∀ b h : ZMod p,
      snorm (v.S c) (b - a) ≤ v.sig η c →
      snorm (insert (r.ξ a) (v.S c)) h ≤ v.sig η c →
      8 * r.m * snorm (insert (r.ξ a) (v.S c)) h ≤ v.ρ c →
      |v.F c (v.Ξ c (b + ((2 * r.m : ℕ) : ZMod p) * h)) -
        v.F c (zmap r.Bᵀ (r.π (v.Ξ c (b + ((2 * r.m : ℕ) : ZMod p) * h) - v.Ξ c b)) +
          v.Ξ c b)| ≤
        p71L (v.S c) (v.G c) η (eps4 η) (v.ρ c) r.m * snorm (insert (r.ξ a) (v.S c)) h *
          ‖(v.G c).emb (fun i => (r.u i : ℝ))‖

/-- The numerical conditions satisfied by a poorly distributed label. -/
def NumOK (c : v.C) (r : RData p (v.G c)) : Prop :=
  0 < v.sig η c ∧ 4 * v.sig η c ≤ v.ρ c / 2 ∧ 0 < v.tau η c ∧ v.tau η c ≤ 1 ∧
    Real.exp (-(1 / η) ^ C5) * v.ρ c ≤ v.tau η c ∧ 4 * (r.m * v.tau η c) ≤ v.sig η c ∧
    50 * (v.S c).card * (r.m * v.tau η c) / v.sig η c +
      50 * (v.S c).card * v.sig η c / (v.ρ c / 2) ≤ η ^ C3 / 4 ∧
    p71L (v.S c) (v.G c) η (eps4 η) (v.ρ c) r.m * (v.tau η c / 2) *
      ‖(v.G c).emb (fun i => (r.u i : ℝ))‖ ≤ η ^ C3 / 4 ∧
    2 ^ ((v.G c).d ^ 2) * (∑ i, 4 * (wM (v.G c) η i : ℝ) / ‖(v.G c).v i‖) ≤
      Real.exp ((1 / η) ^ C3) ∧
    ((2 * r.m : ℕ) : ZMod p) ≠ 0

/-- The condition under which the label `(c, a, t)` is refined. -/
def Ref (c : v.C) (a t : ZMod p) : Prop :=
  v.Poor η c ∧ regP (v.S c) (v.ρ c / 2) (a - v.n c) ≠ 0 ∧ regP (v.S c) (v.sig η c) t ≠ 0

/-- The weight of the label `(c, a, t)`. -/
def rprob (c' : v.C × ZMod p × ZMod p) : ℝ :=
  v.prob c'.1 * regP (v.S c'.1) (v.ρ c'.1 / 2) (c'.2.1 - v.n c'.1) *
    regP (v.S c'.1) (v.sig η c'.1) c'.2.2

open Classical in
/-- The data of the label `(c, a, t)`. -/
def rdata (rd : ∀ c, RData p (v.G c)) (c' : v.C × ZMod p × ZMod p) : LData p :=
  if v.Ref η c'.1 c'.2.1 c'.2.2 then (v.ldata c'.1).refine (rd c'.1) c'.2.1 c'.2.2 (v.tau η c'.1)
  else v.ldata c'.1

/-- The refined structured local approximant. -/
def refined (rd : ∀ c, RData p (v.G c)) : SLA p :=
  ofData (v.C × ZMod p × ZMod p) (v.rprob η) (v.rdata η rd)

variable {v η}

/-! ### Statistics of the refined approximant -/

/-! ### Structural statistics -/

end SLA

end

end GT
end Def_GT_BadDim

section Def_GT_BadEdNum
/-!
# Theorem 6.6, the quadratic case: the numerical bookkeeping
-/

open Finset KM

namespace GT

noncomputable section

/-- The parameter fed to the inverse theorem: `(δ/4)^8` with `δ = η/16`. -/
def edηi (η : ℝ) : ℝ := (η / 16 / 4) ^ 8

/-- The scale ratio. -/
def edθ (s : ℕ) (η : ℝ) : ℝ := u3θ s (edηi η)

/-- The depth. -/
def edT (η : ℝ) : ℕ := u3T (edηi η)

/-- The bound on the dilation. -/
def edK (s : ℕ) (η : ℝ) : ℝ := u3k s (edηi η)

/-- The correlation. -/
def edκ (η : ℝ) : ℝ := u3κ (edηi η)

/-- The total translation error. -/
def edE (η : ℝ) : ℝ := η ^ C3 / 2

/-- The numerical facts used in the proof of Theorem 6.6 (quadratic case), for a label with
`|S| = t ≤ s` and radius `ρ`. -/
structure EdNum (η : ℝ) (s t d2 : ℕ) (ρ : ℝ) (p : ℕ) : Prop where
  n1 : 12 * (SLA.eps4 η * ρ) ≤ ρ / 2
  n2 : 50 * (t : ℝ) * (3 * (SLA.eps4 η * ρ)) / (ρ / 2) ≤ η / 16 / 8
  n3 : 72 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2
  n4 : 50 * (t : ℝ) * (18 * (edθ s η * SLA.eps4 η * ρ)) / (ρ / 2) ≤ η / 16 / 16
  n5 : 72 * (edθ s η * SLA.eps4 η * ρ) ≤ SLA.eps4 η * ρ
  n6 : 50 * (t : ℝ) * (18 * (edθ s η * SLA.eps4 η * ρ)) / (SLA.eps4 η * ρ) ≤ η / 16 / 16
  θpos : 0 < edθ s η
  θle : edθ s η ≤ 1
  ηipos : 0 < edηi η
  ηile : edηi η ≤ 1 / 2 ^ 30
  ρ0pos : 0 < edθ s η * SLA.eps4 η * ρ
  ρ0le : edθ s η * SLA.eps4 η * ρ ≤ 1
  pl : u3P s (edηi η) (edθ s η) (edθ s η * SLA.eps4 η * ρ) ≤ p
  kp : 6 * edK s η < p
  K1 : 1 ≤ edK s η
  e0 : 0 < edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ)
  e1 : 2 * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ)) ≤ 1
  e2 : 4 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤
    edθ s η * SLA.eps4 η * ρ
  e3 : 24 * (edθ s η * SLA.eps4 η * ρ) ≤ ρ / 2
  e4 : 6 * (edθ s η * SLA.eps4 η * ρ) +
    12 * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) ≤ ρ / 2
  e5 : 50 * (t : ℝ) * (edK s η * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))) /
      (edθ s η * SLA.eps4 η * ρ) +
    50 * (t : ℝ) * (6 * (edθ s η * SLA.eps4 η * ρ)) / (ρ / 2) ≤ edE η
  J0 : 0 ≤ u3J (edηi η)
  J1 : u3J (edηi η) ≤ (1 / η) ^ C2
  rm : Real.exp (-(1 / η) ^ C5) * ρ ≤ 2 * (edθ s η ^ edT η * (edθ s η * SLA.eps4 η * ρ))
  vol : 16 * 2 ^ d2 ≤ Real.exp ((1 / η) ^ C3)
  κ0 : 0 ≤ edκ η
  κ1 : edκ η ≤ 1 / 4
  dec : 4 * edE η + η ^ C2 ≤ 3 * edκ η ^ 2 * (η / 16 / 4 * (η / 16))
  E1 : edE η ≤ η ^ C3

section edaux

set_option exponentiation.threshold 2048

variable {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10)
include hη0 hη1

variable {s : ℕ} (hs : (s : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
include hs

end edaux

end

end GT
end Def_GT_BadEdNum

section Def_GT_U3Base
/-!
# Basic tools for the local inverse `U³` theorem

* symmetry of regular distributions;
* `Good T A l`: the character `x ↦ e(l x / p)` is `A`-Lipschitz with respect to `‖·‖_{T^⊥}`
  (a substitute for the word norm of Green–Tao);
* large exponential sums over regular Bohr distributions force goodness;
* a box Cauchy–Schwarz inequality with a general bounded kernel;
* translation estimates for centred regular variables.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Symmetry -/

/-! ### Goodness -/

/-- `l` is `A`-good with respect to `T`: `‖l h / p‖ ≤ A ‖h‖_{T^⊥}` for all `h`. -/
def Good (T : Finset (ZMod p)) (A : ℝ) (l : ZMod p) : Prop := ∀ h, cn (l * h) ≤ A * snorm T h

namespace Good

variable {T : Finset (ZMod p)} {A A' : ℝ} {l l' : ZMod p}

end Good

/-! ### Box Cauchy–Schwarz -/

section box

variable {α β : Type*} [Fintype α] [Fintype β]

end box

/-! ### Translations of centred regular variables -/

end

end GT
end Def_GT_U3Base

section Def_GT_U3S2
/-!
# Local inverse `U³`, second step: `ξ` respects many additive quadruples

(Green–Tao, Theorem 9.2 and Corollary 9.3.)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The linearity defect of `ξ` on a quadruple. -/
def sig (ξ : ZMod p → ZMod p) (q : Fin 4 → ZMod p) : ZMod p := ξ (q 0) + ξ (q 1) - ξ (q 2) - ξ (q 3)

end

end GT
end Def_GT_U3S2

section Def_GT_U3Back
/-!
# Local inverse `U³`: the last three steps combined

From the correlation estimate of Proposition 9.10 (for a frequency function `ξ''` which is
linear on a Bohr set up to a good error) we derive the correlation with a locally quadratic phase,
chaining the seventh, eighth and ninth steps.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The error of the seventh step. -/
def err7 (S T : Finset (ZMod p)) (B ρ0 r' r3 ρ4 ρ5 ρ6 : ℝ) : ℝ :=
  50 * T.card * ρ6 / r' + 2 * (50 * T.card * ρ5 / ρ4) + 50 * S.card * ρ4 / ρ0 +
    2 * (2 * Real.pi * (B * ρ5)) +
    2 * (2 * Real.pi * (B * ρ5 * (50 * T.card * T.card * (2 ^ (T.card ^ 2) * T.card) * ρ6 / r3
      + 1)))

/-- The parameter `δ` of the eighth step. -/
def del8 (T : Finset (ZMod p)) (c0 ρ5 ρ6 : ℝ) : ℝ := (c0 / 2) ^ 2 - 100 * T.card * ρ6 / ρ5

/-- The bound on the dilation `q` of the eighth step. -/
def qbar (T : Finset (ZMod p)) (c0 ρ5 ρ6 : ℝ) : ℝ := (32 / del8 T c0 ρ5 ρ6 ^ 4) ^ (T.card ^ 2)

/-- The error of the first half of the ninth step. -/
def err9 (T : Finset (ZMod p)) (c0 ρ5 ρ6 ρ9 ρ10 : ℝ) : ℝ :=
  2 * (50 * T.card * ((2 * qbar T c0 ρ5 ρ6) * ρ10) / ρ5) +
    50 * T.card * ((2 * qbar T c0 ρ5 ρ6) * ρ9) / ρ6 +
    2 * (2 * Real.pi * ((2 * qbar T c0 ρ5 ρ6) *
      (lqK T.card (del8 T c0 ρ5 ρ6 ^ 4) ρ6 * ρ9 * ρ10)))

end

end GT
end Def_GT_U3Back

section Def_GT_U3Q
/-!
# Centred random additive quadruples

(Green–Tao, Corollary 9.3.)  A random additive quadruple centred at `c` with frequencies `T`
and scales `r2 ≤ r3 ≤ r4` is `qd c x2 x3 x4` with `x2, x3, x4` drawn independently and
regularly from `B(T, r2)`, `B(T, r3)`, `B(T, r4)`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The additive quadruple with centre `c` (only `c 1, c 2, c 3` matter) and offsets
`x2, x3, x4`. -/
def qd (c : Fin 4 → ZMod p) (x2 x3 x4 : ZMod p) : Fin 4 → ZMod p :=
  ![c 2 + c 3 - c 1 + x3 + x4 - x2, c 1 + x2, c 2 + x3, c 3 + x4]

/-- Average of `F` over a random additive quadruple centred at `c`. -/
def qavg (T : Finset (ZMod p)) (r2 r3 r4 : ℝ) (c : Fin 4 → ZMod p)
    (F : (Fin 4 → ZMod p) → ℝ) : ℝ :=
  ∑ x2, ∑ x3, ∑ x4, regP T r2 x2 * regP T r3 x3 * regP T r4 x4 * F (qd c x2 x3 x4)

/-! ### A general translation estimate inside a context -/

end

end GT
end Def_GT_U3Q

section Def_GT_U3Eq
/-!
# Equidistribution of `λ ↦ (λ q₀, λ q₁, λ q₂)` in boxes

Used for the random filters of Green–Tao, Theorem 9.4.  If `(q₀, q₁, q₂)` satisfies no
relation `∑ kᵢ qᵢ = 0` with `0 < max |kᵢ| < 2M`, then for uniformly random `λ ∈ ℤ/pℤ` the
probability that `λ qᵢ + xᵢ` lies in `{cn ≤ ε}` for `i = 0, 1, 2` is close to the product of
the densities.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Counting `{y : cn y ≤ r}` -/

/-! ### Trapezoidal cut-offs -/

/-! ### The equidistribution estimate -/

/-! ### Box probabilities -/

/-- The genericity bound used for the filters. -/
def gM (m : ℕ) : ℕ := 2 * 10 ^ 12 * m ^ 2

end

end GT
end Def_GT_U3Eq

section Def_GT_U3S3
/-!
# Local inverse `U³`, third step: random filters

(Green–Tao, Theorem 9.4.)  Random linear filters `Ξ(n) = λ n + ξ(n) h` keep additive quadruples
respected by `ξ` with probability `≈ 10⁻⁶` each, and very bad quadruples with probability at
most about half of that.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Doubling -/

/-! ### One filter -/

/-! ### Non-generic quadruples are rare -/

/-! ### Many filters -/

open Classical in
/-- The penalised weight of Theorem 9.4. -/
def Wt (S : Finset (ZMod p)) (ρv L : ℝ) (ξ : ZMod p → ZMod p) (A : Fin 4 → Finset (ZMod p))
    (q : Fin 4 → ZMod p) : ℝ :=
  (if ∀ i, q i ∈ A i then 1 else 0) * (1 - L * (if Good S (1 / ρv) (sig ξ q) then 0 else 1))

end

end GT
end Def_GT_U3S3

section Def_GT_U3S4a
/-!
# Local inverse `U³`, fourth step: averages over three regular variables

Tools for the energy-decrement (score maximisation) argument of Green–Tao, Theorem 9.5:
averages `avg3` over three independent regular variables, translations inside them, and the
marginal distributions of the components of a random additive quadruple.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

section pos

variable {T : Finset (ZMod p)} {s2 s3 s4 : ℝ} (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hs2 hs3 hs4

end pos

/-! ### Marginals of a random additive quadruple -/

/-- The centre of the `i`-th component. -/
def cent (c : Fin 4 → ZMod p) (i : Fin 4) : ZMod p := qd c 0 0 0 i

section marg

variable {T : Finset (ZMod p)} {s2 s3 s4 : ℝ} (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4)
include hs2 hs3 hs4

end marg

/-! ### Fubini and absorption -/

end

end GT
end Def_GT_U3S4a

section Def_GT_U3S4b
/-!
# Local inverse `U³`, fourth step: a large local `U²` norm gives an energy increment

This is the estimate (bb) in the proof of Green–Tao, Theorem 9.5.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The local `U²`-type average of a real function `g` around the base point `u`. -/
def U2f (T : Finset (ZMod p)) (ρ0 ρ1 : ℝ) (g : ZMod p → ℝ) (u : ZMod p) : ℝ :=
  ∑ h0, ∑ h0', ∑ h1, ∑ h1', regP T ρ0 h0 * regP T ρ0 h0' * regP T ρ1 h1 * regP T ρ1 h1' *
    (g (u + h0 + h1) * g (u + h0 + h1') * g (u + h0' + h1) * g (u + h0' + h1'))

end

end GT
end Def_GT_U3S4b

section Def_GT_U3S4c
/-!
# Local inverse `U³`, fourth step: neighbourhoods, energies and the score

Definitions for the score maximisation argument of Green–Tao, Theorem 9.5, and the
stability of the weighted average `QW` under the random refinement.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Scales -/

section scales

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRθ : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
include hR0 hRθ hθ0 hθ1

end scales

/-! ### Neighbourhoods -/

/-- The levels `l_i` of the four components. -/
def lvl : Fin 4 → ℕ := ![0, 2, 1, 0]

/-- Indicator function. -/
def ind (A : Finset (ZMod p)) (u : ZMod p) : ℝ := if u ∈ A then 1 else 0

/-- The density `α_i` of `A_i` at the neighbourhood `(c, j, T)`. -/
def alph (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (i : Fin 4) : ℝ :=
  ∑ u, regP T (R (j + lvl i)) (u - cent c i) * ind (A i) u

/-- The balanced function `1_{A_i} - α_i`. -/
def bal (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (i : Fin 4) (u : ZMod p) : ℝ :=
  ind (A i) u - alph R A T c j i

/-- The average of the weight `W` at the neighbourhood `(c, j, T)`. -/
def QW (R : ℕ → ℝ) (W : (Fin 4 → ZMod p) → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) : ℝ :=
  qavg T (R (j + 2)) (R (j + 1)) (R j) c W

/-! ### Stability of `QW` under the random refinement -/

section stab

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16)
include hR0 hRk hθ0 hθ1

end stab

end

end GT
end Def_GT_U3S4c

section Def_GT_U3S5b
/-!
# Local inverse `U³`, fifth step: a frequency function `ξ'` on a Bohr neighbourhood

Green–Tao, Theorem 9.7.  From the pseudorandom neighbourhood of the fourth step we build
`ξ'(a) = ξ(a₃(a)) + ξ(a - a₃(a))` for all `a` outside a small exceptional set, such that
`ξ'(a) ≈ ξ(a - a₂) + ξ(a₂)` for all but a small proportion (relative to `α₁α₂`) of the
decompositions `a = (a - a₂) + a₂` with `a - a₂ ∈ A₁`, `a₂ ∈ A₂`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Elementary probability -/

section prob

variable {α : Type*} [Fintype α] {P : α → ℝ} (hP : ∀ x, 0 ≤ P x) (hP1 : ∑ x, P x = 1)
include hP

include hP1

end prob

/-! ### The data of the fifth step -/

/-- `1_{A₁}(a - a₂) 1_{A₂}(a₂)`. -/
def I12 (A : Fin 4 → Finset (ZMod p)) (a a2 : ZMod p) : ℝ := ind (A 0) (a - a2) * ind (A 1) a2

/-- The centre `a₁ = a_{(1),1} + a_{(2),1}` of the Bohr neighbourhood of Theorem 9.7. -/
def aC (c : Fin 4 → ZMod p) : ZMod p := cent c 0 + cent c 1

/-- `g₁₂(a) = E 1_{A₁}(a - a₂) 1_{A₂}(a₂)`. -/
def g12 (R : ℕ → ℝ) (A : Fin 4 → Finset (ZMod p)) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p)
    (j : ℕ) (a : ZMod p) : ℝ :=
  ∑ x, regP T (R (j + 2)) x * I12 A a (cent c 1 + x)

open Classical in
/-- The indicator of a very bad quadruple. -/
def vb (S : Finset (ZMod p)) (ρv : ℝ) (l : ZMod p) : ℝ := if Good S (1 / ρv) l then 0 else 1

end

end GT
end Def_GT_U3S5b

section Def_GT_U3S6d
/-!
# Local inverse `U³`, Proposition 9.8 (`ξ'` respects almost all additive quadruples)
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-- The triple average `E_h E_a E_b` of Proposition 9.8. -/
def E3 (R : ℕ → ℝ) (T : Finset (ZMod p)) (c : Fin 4 → ZMod p) (j : ℕ)
    (F : ZMod p → ZMod p → ZMod p → ℝ) : ℝ :=
  ∑ h, regP T (R (j + 3)) h * ∑ a, regP T (R j) (a - aC c) * ∑ b, regP T (R j) (b - aC c) *
    F h a b

section pordo

variable {R : ℕ → ℝ} {θ : ℝ} (hR0 : ∀ t, 0 < R t) (hRk : ∀ t, R (t + 1) ≤ θ * R t)
  (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 16) {T : Finset (ZMod p)} {A : Fin 4 → Finset (ZMod p)}
  {c : Fin 4 → ZMod p} {j : ℕ} {ε4 : ℝ}
  (hPR : ∀ i, ∑ u, regP T (R (j + lvl i)) (u - cent c i) *
    U2f T (R (j + 10)) (R (j + 11)) (bal R A T c j i) u ≤ ε4)
include hR0 hRk hθ0 hθ1 hPR

end pordo

end

end GT
end Def_GT_U3S6d

section Def_GT_InvU3Num
/-!
# Numerical bookkeeping for the local inverse `U³` theorem

All the scale conditions have the form `θ * M ≤ ε`, where `M` is at most a fixed power of the
huge quantity `H = exp(D³)`, `D = s + J + 1`, `ε` is at least a fixed negative power of `H`, and
`θ ≤ exp(-D⁴) ≤ H^{-2^29}`.
-/

open Finset KM

namespace GT

noncomputable section

/-- The number of random filters. -/
def u3m (η : ℝ) : ℕ := 8 * (Nat.log 2 ⌊1 / η⌋₊ + 1) + 60

/-- The penalty. -/
def u3L : ℝ := 10 ^ 6

/-- The density after the third step. -/
def u3c3 (η : ℝ) : ℝ := (1 / 10 ^ 6) ^ u3m η * (η ^ 8 / 2 ^ 26) / 4

section basic

variable {s : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

end basic

/-! ### The number of filters and the density -/

section filters

variable {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2 ^ 30)
include hη0 hη

end filters

end

end GT
end Def_GT_InvU3Num


