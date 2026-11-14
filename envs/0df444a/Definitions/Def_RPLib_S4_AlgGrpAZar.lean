-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpAZar
-- name    : RPLib_S4_AlgGrpAZar
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:33:50.561036+00:00
-- url     : https://prove2.me/theorems/c62fa33c-7f5c-432f-b61e-08168cef713f
-- title:
--   Larsen's alternative library: the Zariski topology on `GL_n(K)`
-- statement:
--   `GL_n` is the closed subvariety `{(A, B) | A B = 1}` of affine `2 n^2`-space, so its coordinate
--   functions are the entries of `g` and of `g⁻¹` (`crd`). The Zariski topology `zarTop` on the points
--   `GL n K` (any field `K`) is induced from `Spec K[Var n]`; it is given as an `abbrev`, to be used as a
--   local instance (`attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop`), so that it never
--   clashes with other topologies on `GL n K`.
--
--   Main results: closed sets are exactly the zero sets `zeroS S` of sets of polynomials, the closure of
--   `Z` is `zeroS (vanI Z)`, the space is Noetherian and T1, maps given by polynomials in the coordinates
--   are continuous, and translations and inversion make `GL n K` a `SemiTopGroup`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpASemi

/-!
# S4-AlgGrpA, file Zar: the Zariski topology on `GL_n(K)`

`GL_n` is the closed subvariety `{(A, B) | A B = 1}` of affine `2 n^2`-space, so its coordinate
functions are the entries of `g` and of `g⁻¹` (`crd`). The Zariski topology `zarTop` on the points
`GL n K` (any field `K`) is induced from `Spec K[Var n]`; it is given as an `abbrev`, to be used as a
local instance (`attribute [local instance] RamanujanPetersson.AlgGrpA.zarTop`), so that it never
clashes with other topologies on `GL n K`.

Main results: closed sets are exactly the zero sets `zeroS S` of sets of polynomials, the closure of
`Z` is `zeroS (vanI Z)`, the space is Noetherian and T1, maps given by polynomials in the coordinates
are continuous, and translations and inversion make `GL n K` a `SemiTopGroup`.
-/

set_option autoImplicit false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpA

/-- Coordinate variables of `GL_n`: entries of `g` (left summand) and of `g⁻¹` (right summand). -/
abbrev Var (n : Type*) := (n × n) ⊕ (n × n)

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Coordinates of `g ∈ GL_n(K)`: the entries of `g` and of `g⁻¹`. -/
def crd (g : Matrix.GeneralLinearGroup n K) : Var n → K :=
  Sum.elim (fun ij => (g : Matrix n n K) ij.1 ij.2)
    (fun ij => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2)

@[simp] theorem crd_inl (g : Matrix.GeneralLinearGroup n K) (ij : n × n) :
    crd g (Sum.inl ij) = (g : Matrix n n K) ij.1 ij.2 := rfl

@[simp] theorem crd_inr (g : Matrix.GeneralLinearGroup n K) (ij : n × n) :
    crd g (Sum.inr ij) = ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2 := rfl

/-- The `K`-point of `Spec K[Var n]` attached to `g`. -/
def toSpec (g : Matrix.GeneralLinearGroup n K) : PrimeSpectrum (MvPolynomial (Var n) K) :=
  ⟨RingHom.ker (MvPolynomial.eval (crd g)), RingHom.ker_isPrime _⟩

/-- The Zariski topology on `GL_n(K)`. -/
abbrev zarTop : TopologicalSpace (Matrix.GeneralLinearGroup n K) :=
  TopologicalSpace.induced toSpec inferInstance

attribute [local instance] zarTop

/-- The zero set in `GL_n(K)` of a set of polynomials in the coordinates. -/
def zeroS (S : Set (MvPolynomial (Var n) K)) : Set (Matrix.GeneralLinearGroup n K) :=
  {g | ∀ p ∈ S, eval (crd g) p = 0}

/-- The ideal of polynomials vanishing on `Z`. -/
def vanI (Z : Set (Matrix.GeneralLinearGroup n K)) : Ideal (MvPolynomial (Var n) K) :=
  ⨅ g ∈ Z, RingHom.ker (MvPolynomial.eval (crd g))

theorem mem_zeroS {S : Set (MvPolynomial (Var n) K)} {g : Matrix.GeneralLinearGroup n K} :
    g ∈ zeroS S ↔ ∀ p ∈ S, eval (crd g) p = 0 := Iff.rfl

theorem mem_vanI {Z : Set (Matrix.GeneralLinearGroup n K)} {p : MvPolynomial (Var n) K} :
    p ∈ vanI Z ↔ ∀ g ∈ Z, eval (crd g) p = 0 := by
  simp [vanI, Submodule.mem_iInf, RingHom.mem_ker]

theorem preimage_zeroLocus (S : Set (MvPolynomial (Var n) K)) :
    toSpec ⁻¹' PrimeSpectrum.zeroLocus S = zeroS (n := n) S := by
  ext g
  simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, toSpec, Set.subset_def,
    SetLike.mem_coe, RingHom.mem_ker, mem_zeroS]

theorem isClosed_iff {Z : Set (Matrix.GeneralLinearGroup n K)} :
    IsClosed Z ↔ ∃ S : Set (MvPolynomial (Var n) K), Z = zeroS S := by
  rw [isClosed_induced_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus t).mp ht
    exact ⟨S, preimage_zeroLocus S⟩
  · rintro ⟨S, rfl⟩
    exact ⟨_, PrimeSpectrum.isClosed_zeroLocus S, preimage_zeroLocus S⟩

theorem isClosed_zeroS (S : Set (MvPolynomial (Var n) K)) : IsClosed (zeroS (n := n) S) :=
  isClosed_iff.2 ⟨S, rfl⟩

theorem zeroS_vanI_of_isClosed {Z : Set (Matrix.GeneralLinearGroup n K)} (hZ : IsClosed Z) :
    zeroS (vanI Z : Set (MvPolynomial (Var n) K)) = Z := by
  obtain ⟨S, rfl⟩ := isClosed_iff.1 hZ
  ext g
  constructor
  · intro hg p hp
    exact hg p (mem_vanI.2 fun h hh => hh p hp)
  · intro hg p hp
    exact (mem_vanI.1 hp) g hg

theorem closure_eq_zeroS_vanI (Z : Set (Matrix.GeneralLinearGroup n K)) :
    closure Z = zeroS (vanI Z : Set (MvPolynomial (Var n) K)) := by
  apply le_antisymm
  · exact closure_minimal (fun g hg p hp => mem_vanI.1 hp g hg) (isClosed_zeroS _)
  · intro g hg
    have h := zeroS_vanI_of_isClosed (isClosed_closure (s := Z))
    rw [← h]
    exact fun p hp => hg p (mem_vanI.2 fun h hh => mem_vanI.1 hp h (subset_closure hh))

instance noetherianSpace : TopologicalSpace.NoetherianSpace (Matrix.GeneralLinearGroup n K) :=
  Topology.IsInducing.noetherianSpace (i := toSpec) ⟨rfl⟩

instance t1Space : T1Space (Matrix.GeneralLinearGroup n K) := by
  refine ⟨fun g => isClosed_iff.2 ⟨Set.range (fun ij : n × n =>
    X (Sum.inl ij) - C ((g : Matrix n n K) ij.1 ij.2)), ?_⟩⟩
  ext h
  simp only [Set.mem_singleton_iff, mem_zeroS, Set.forall_mem_range, map_sub, eval_X, eval_C,
    crd_inl, sub_eq_zero]
  constructor
  · rintro rfl ij
    rfl
  · intro H
    exact Units.ext (Matrix.ext fun i j => H (i, j))

/-- A map whose coordinates are polynomials in the coordinates is continuous. -/
theorem continuous_of_poly {m : Type*} [Fintype m] [DecidableEq m]
    (φ : Matrix.GeneralLinearGroup n K → Matrix.GeneralLinearGroup m K)
    (q : Var m → MvPolynomial (Var n) K) (hq : ∀ g v, crd (φ g) v = eval (crd g) (q v)) :
    Continuous φ := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨S, rfl⟩ := isClosed_iff.1 hZ
  refine isClosed_iff.2 ⟨(bind₁ q) '' S, ?_⟩
  have key : ∀ g p, eval (crd (φ g)) p = eval (crd g) (bind₁ q p) := by
    intro g p
    have h1 : (fun v => crd (φ g) v) = fun v => eval (crd g) (q v) := funext (hq g)
    change eval (crd (φ g)) p = eval₂Hom (RingHom.id K) (crd g) (bind₁ q p)
    rw [eval₂Hom_bind₁]
    change eval (crd (φ g)) p = eval (fun i => eval (crd g) (q i)) p
    rw [← h1]
  ext g
  simp only [Set.mem_preimage, mem_zeroS, Set.forall_mem_image, key]

theorem continuous_mul_left (a : Matrix.GeneralLinearGroup n K) :
    Continuous (fun g : Matrix.GeneralLinearGroup n K => a * g) := by
  refine continuous_of_poly _ (Sum.elim
    (fun ij => ∑ k, C ((a : Matrix n n K) ij.1 k) * X (Sum.inl (k, ij.2)))
    (fun ij => ∑ k, X (Sum.inr (ij.1, k)) *
      C (((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) k ij.2))) ?_
  rintro g (⟨i, j⟩ | ⟨i, j⟩)
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, mul_inv_rev]

theorem continuous_mul_right (a : Matrix.GeneralLinearGroup n K) :
    Continuous (fun g : Matrix.GeneralLinearGroup n K => g * a) := by
  refine continuous_of_poly _ (Sum.elim
    (fun ij => ∑ k, X (Sum.inl (ij.1, k)) * C ((a : Matrix n n K) k ij.2))
    (fun ij => ∑ k, C (((a⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 k) *
      X (Sum.inr (k, ij.2)))) ?_
  rintro g (⟨i, j⟩ | ⟨i, j⟩)
  · simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, mul_inv_rev]

theorem continuous_inv' : Continuous (fun g : Matrix.GeneralLinearGroup n K => g⁻¹) := by
  refine continuous_of_poly _ (fun v => X v.swap) ?_
  rintro g (⟨i, j⟩ | ⟨i, j⟩)
  · simp
  · simp

instance semiTopGroup : SemiTopGroup (Matrix.GeneralLinearGroup n K) where
  cont_mul_left := continuous_mul_left
  cont_mul_right := continuous_mul_right
  cont_inv := continuous_inv'

end RamanujanPetersson.AlgGrpA

end


