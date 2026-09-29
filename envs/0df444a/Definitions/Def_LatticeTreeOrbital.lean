-- Prove2me | Definitions.Def_LatticeTreeOrbital
-- name    : LatticeTreeOrbital
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/9a359fa6-34ba-5320-b376-098af40df9fb
-- title:
--   Lattices, homothety vertices and twisted actions for GL2​
-- statement:
--   For a commutative ring $R$ and a field $K$ that is an $R$-algebra, `stdLattice R K` is the $R$-submodule of $K^2$ of vectors all of whose coordinates lie in the image of $R$ (Mathlib's `IsLocalization.IsInteger`); it is finitely generated, spanned by the standard basis vectors, and $K$-spans $K^2$. For $g\in\mathrm{GL}_2(K)$, `mulVecLinR g` is the $R$-linear map $v\mapsto g\,v$ and `latticeMap g L` the image submodule, giving a monoid action with the expected monotonicity and strict-monotonicity properties. `IsFullLattice L` is the conjunction: $L$ finitely generated and $\mathrm{span}_K L=\top$. `scalarGL c` is $c\cdot 1$ for $c\in K^\times$ and `diagSnd x` the diagonal matrix $\mathrm{diag}(1,x)$. `Homothetic L L'` means $cL=L'$ for some $c\in K^\times$; this is an equivalence relation on the subtype `FullLattice` of full lattices, and `Vertex R K` is the quotient, with base point `stdVertex`, constructor `Vertex.mk`, and the induced action `Vertex.act`. The stabiliser of `stdVertex` is characterised as the set of $g$ with $cg$ integral for some scalar $c$. With $R\to K$ a fraction field, `unitOfNeZero` turns $\varpi\neq0$ into a unit of $K$; `AdjacentLattice L L'` asserts $\varpi L< L'< L$ for some irreducible $\varpi$, and `interLattice R K ϖ c d` is the lattice of integral vectors with $d v_0-c v_1\equiv 0 \pmod\varpi$. The family `neighborOfOption`, indexed by $\mathrm{Option}(R/\varpi)$, is an injection into the lattices strictly between $\varpi R^2$ and $R^2$; a companion bijection identifies the proper nonzero subspaces of a two-dimensional space with its projectivisation, of cardinality $\#k+1$.
--
--   `IntegralAut R K` is a structure bundling a ring automorphism of $K$, one of $R$, and the compatibility of the two over $\mathrm{algebraMap}$; it acts coordinatewise on vectors (`galVec`), on lattices (`latticeGal`, fixing `stdLattice`) and on vertices, and entrywise on $\mathrm{GL}_2(K)$ (`mapGL`). `twistedLatticeMap δ σ L` $= \delta\,\sigma(L)$ composes with a cocycle twist, whence the norms `normTwo` $=\delta\,\sigma(\delta)$ and `normThree` $=\delta\,\sigma(\delta)\,\sigma^2(\delta)$ and the statement that a $(\delta,\sigma)$-fixed lattice is fixed by the norm when $\sigma^3=\mathrm{id}$. Complex conjugation is recorded as an example of such an automorphism of order two. Finally `IsFixedVertex g v` is $g\cdot v=v$, `fixedVertexSet g` the set of such vertices, and `unitOrbitalCount R g` its cardinality as a natural number — the project's definition of the unit orbital integral as a count of fixed vertices; it is invariant under conjugation, and scalars fix every vertex.
--
--   **Relation to Mathlib.** Mathlib has no Bruhat–Tits tree or lattice-class formalism for $\mathrm{GL}_2$; the lattices, homothety vertices, adjacency and fixed-vertex counts here are the project's own, built on Mathlib's `Submodule`, `Matrix.GeneralLinearGroup`, `IsLocalization.IsInteger` and `Projectivization` (whose cardinality result supplies the count $\#k+1$). `IntegralAut` is the project's bundling of a ring automorphism of $K$ together with a compatible automorphism of $R$, rather than a Mathlib structure.
--
--   **Where it is used.** The vertex set with its $\mathrm{GL}_2(K)$-action and twisted action provides the combinatorial model in which unit orbital integrals and twisted orbital integrals are expressed as fixed-point counts, as needed for the cyclic base-change comparison underlying the Langlands–Tunnell input to the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LatticeTreeOrbital.lean

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

section Helpers

variable {α : Type*} [CommRing α]

theorem mulVec_single_one (M : Matrix (Fin 2) (Fin 2) α) (j : Fin 2) :
    M *ᵥ (Pi.single j 1) = fun i => M i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']

theorem diagonal_mulVec (d v : Fin 2 → α) :
    Matrix.diagonal d *ᵥ v = fun i => d i * v i := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq]

end Helpers

variable (R : Type*) [CommRing R]
variable (K : Type*) [Field K] [Algebra R K]

def stdLattice : Submodule R (Fin 2 → K) where
  carrier := {v | ∀ i, IsLocalization.IsInteger R (v i)}
  add_mem' := fun hv hw i => IsLocalization.isInteger_add (hv i) (hw i)
  zero_mem' := fun _ => IsLocalization.isInteger_zero
  smul_mem' := fun r v hv i => by
    rw [Pi.smul_apply]
    exact IsLocalization.isInteger_smul (hv i)

theorem mem_stdLattice {v : Fin 2 → K} :
    v ∈ stdLattice R K ↔ ∀ i, IsLocalization.IsInteger R (v i) := Iff.rfl

attribute [local simp] mem_stdLattice
theorem single_one_mem_stdLattice (j : Fin 2) :
    (Pi.single j 1 : Fin 2 → K) ∈ stdLattice R K := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same]
    exact IsLocalization.isInteger_one
  · rw [Pi.single_eq_of_ne h]
    exact IsLocalization.isInteger_zero

theorem stdLattice_eq_span :
    stdLattice R K = Submodule.span R (Set.range fun j => (Pi.single j 1 : Fin 2 → K)) := by
  apply le_antisymm
  · intro v hv
    choose w hw using hv
    have hv' : v = w 0 • (Pi.single 0 1 : Fin 2 → K) + w 1 • (Pi.single 1 1 : Fin 2 → K) := by
      funext i
      have h0 : algebraMap R K (w 0) = v 0 := hw 0
      have h1 : algebraMap R K (w 1) = v 1 := hw 1
      fin_cases i <;>
        simp [Algebra.smul_def, ← h0, ← h1]
    rw [hv']
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact single_one_mem_stdLattice R K j

theorem stdLattice_fg : (stdLattice R K).FG := by
  rw [Submodule.fg_def]
  exact ⟨Set.range fun j => (Pi.single j 1 : Fin 2 → K), Set.finite_range _,
    (stdLattice_eq_span R K).symm⟩

theorem stdLattice_span_top :
    Submodule.span K ((stdLattice R K : Set (Fin 2 → K))) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (by
    simpa only [Pi.basisFun_apply, SetLike.mem_coe] using single_one_mem_stdLattice R K j)

variable {R K}

def mulVecLinR (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

@[simp] theorem mulVecLinR_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinR (R := R) g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

def latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) :=
  L.map (mulVecLinR g)

theorem mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap g L ↔ ∃ w ∈ L, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = v :=
  Submodule.mem_map

theorem mulVec_mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {w : Fin 2 → K} (hw : w ∈ L) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap g L :=
  ⟨w, hw, rfl⟩

theorem mulVecLinR_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    mulVecLinR (R := R) (g * h) = (mulVecLinR g).comp (mulVecLinR h) :=
  LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, mulVecLinR_apply, mulVecLinR_apply, mulVecLinR_apply,
      Matrix.mulVec_mulVec, Units.val_mul]

theorem latticeMap_one (L : Submodule R (Fin 2 → K)) : latticeMap 1 L = L := by
  have h : ∀ v : Fin 2 → K, mulVecLinR (R := R) 1 v = v := fun v => by
    rw [mulVecLinR_apply, Units.val_one, Matrix.one_mulVec]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show mulVecLinR (R := R) 1 w = w from h w]
    exact hw
  · intro hv
    exact ⟨v, hv, h v⟩

attribute [local simp] latticeMap_one
theorem latticeMap_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  unfold latticeMap
  rw [mulVecLinR_mul, Submodule.map_comp]

theorem latticeMap_inv_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g⁻¹ (latticeMap g L) = L := by
  rw [← latticeMap_mul, inv_mul_cancel, latticeMap_one]

theorem latticeMap_latticeMap_inv (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g (latticeMap g⁻¹ L) = L := by
  rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]

theorem latticeMap_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (latticeMap (R := R) g) :=
  Function.LeftInverse.injective (latticeMap_inv_latticeMap g)

theorem latticeMap_mono (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : L ≤ L') : latticeMap g L ≤ latticeMap g L' :=
  Submodule.map_mono h

theorem le_of_latticeMap_le (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : latticeMap g L ≤ latticeMap g L') : L ≤ L' := by
  have := latticeMap_mono g⁻¹ h
  rwa [latticeMap_inv_latticeMap, latticeMap_inv_latticeMap] at this

theorem latticeMap_lt_latticeMap_iff (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} : latticeMap g L < latticeMap g L' ↔ L < L' := by
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_latticeMap_le g h.1) (fun hEq => h.ne (by rw [hEq]))
  · intro h
    exact lt_of_le_of_ne (latticeMap_mono g h.1)
      (fun hEq => h.ne (latticeMap_injective g hEq))

def IsFullLattice (L : Submodule R (Fin 2 → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin 2 → K)) = ⊤

theorem isFullLattice_stdLattice : IsFullLattice (stdLattice R K) :=
  ⟨stdLattice_fg R K, stdLattice_span_top R K⟩

theorem IsFullLattice.map {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : IsFullLattice (latticeMap g L) := by
  refine ⟨hL.1.map _, ?_⟩
  rw [eq_top_iff]
  intro v _

  have hv : v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [hv]
  have hw : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈
      Submodule.span K (L : Set (Fin 2 → K)) := hL.2 ▸ Submodule.mem_top
  refine Submodule.span_induction
    (p := fun w _ => (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
      Submodule.span K ((latticeMap g L : Set (Fin 2 → K)))) ?_ ?_ ?_ ?_ hw
  · intro x hx
    exact Submodule.subset_span (mulVec_mem_latticeMap hx)
  · simp only [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simp only [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    simp only [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

theorem isInteger_apply_of_mem_range {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (i j : Fin 2) : IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, (Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j h).symm⟩

theorem latticeMap_le_stdLattice_of_isInteger {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) :
    latticeMap g (stdLattice R K) ≤ stdLattice R K := by
  rintro _ ⟨w, hw, rfl⟩
  intro i
  show IsLocalization.IsInteger R (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
  have hcoord : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i =
      (g : Matrix (Fin 2) (Fin 2) K) i 0 * w 0 +
        (g : Matrix (Fin 2) (Fin 2) K) i 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcoord]
  exact IsLocalization.isInteger_add
    (IsLocalization.isInteger_mul (hg i 0) (hw 0))
    (IsLocalization.isInteger_mul (hg i 1) (hw 1))

def scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨(c : K) • 1, ((c⁻¹ : Kˣ) : K) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.mul_inv,
        one_smul], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.inv_mul,
        one_smul]⟩

@[simp] theorem scalarGL_coe (c : Kˣ) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := rfl

theorem scalarGL_mulVec (c : Kˣ) (v : Fin 2 → K) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      (c : K) • v := by
  rw [scalarGL_coe, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem scalarGL_mul (c c' : Kˣ) :
    (scalarGL (c * c') : Matrix.GeneralLinearGroup (Fin 2) K) = scalarGL c * scalarGL c' := by
  ext1
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul]

theorem scalarGL_one : (scalarGL (1 : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
  ext1
  rw [scalarGL_coe, Units.val_one, one_smul, Units.val_one]

theorem scalarGL_mul_comm (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL c * g = g * scalarGL c := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem mem_latticeMap_scalarGL {c : Kˣ} {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL c) L ↔ ∃ w ∈ L, (c : K) • w = v := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (scalarGL_mulVec c w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, scalarGL_mulVec c w⟩

def diagSnd (x : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![1, (x : K)], Matrix.diagonal ![1, ((x⁻¹ : Kˣ) : K)], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

@[simp] theorem diagSnd_coe (x : Kˣ) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![1, (x : K)] := rfl

theorem diagSnd_mulVec (x : Kˣ) (v : Fin 2 → K) :
    ((diagSnd x : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      ![v 0, (x : K) * v 1] := by
  rw [diagSnd_coe, diagonal_mulVec]
  funext i
  fin_cases i <;> simp

theorem mem_latticeMap_diagSnd_stdLattice {x : Kˣ} {v : Fin 2 → K} :
    v ∈ latticeMap (diagSnd x) (stdLattice R K) ↔
      IsLocalization.IsInteger R (v 0) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧ (x : K) * w = v 1 := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [diagSnd_mulVec]
    exact ⟨by simpa using hw 0, w 1, hw 1, by simp⟩
  · rintro ⟨h0, w1, hw1, hw1'⟩
    refine ⟨![v 0, w1], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using h0
      · simpa using hw1
    · rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp [hw1']

theorem single_zero_one_mem_latticeMap_diagSnd (x : Kˣ) :
    (Pi.single 0 1 : Fin 2 → K) ∈ latticeMap (diagSnd x) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  refine ⟨by rw [Pi.single_eq_same]; exact IsLocalization.isInteger_one,
    0, IsLocalization.isInteger_zero, ?_⟩
  rw [mul_zero, Pi.single_eq_of_ne]
  decide

def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ c : Kˣ, latticeMap (scalarGL c) L = L'

theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L :=
  ⟨1, by rw [scalarGL_one, latticeMap_one]⟩

theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') :
    Homothetic L' L := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c⁻¹, by
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]⟩

theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') (h' : Homothetic L' L'') : Homothetic L L'' := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c' * c, by rw [scalarGL_mul, latticeMap_mul]⟩

theorem IsFullLattice.of_homothetic {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (h : Homothetic L L') : IsFullLattice L' := by
  obtain ⟨c, rfl⟩ := h
  exact hL.map _

variable (R K) in

def FullLattice : Type _ := {L : Submodule R (Fin 2 → K) // IsFullLattice L}

variable (R K) in

def homothetySetoid : Setoid (FullLattice R K) where
  r L L' := Homothetic L.1 L'.1
  iseqv := ⟨fun L => Homothetic.refl L.1, Homothetic.symm, Homothetic.trans⟩

variable (R K) in

def Vertex : Type _ := Quotient (homothetySetoid R K)

variable (R K) in

def Vertex.mk (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) : Vertex R K :=
  Quotient.mk (homothetySetoid R K) ⟨L, hL⟩

variable (R K) in

def stdVertex : Vertex R K := Vertex.mk R K (stdLattice R K) isFullLattice_stdLattice

theorem Vertex.mk_eq_mk_iff {L L' : Submodule R (Fin 2 → K)} {hL : IsFullLattice L}
    {hL' : IsFullLattice L'} :
    Vertex.mk R K L hL = Vertex.mk R K L' hL' ↔ Homothetic L L' :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

def Vertex.act (g : Matrix.GeneralLinearGroup (Fin 2) K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeMap g L.1, L.2.map g⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      exact ⟨c, by
        show latticeMap (scalarGL c) (latticeMap g L) = latticeMap g L'
        rw [← latticeMap_mul, scalarGL_mul_comm, latticeMap_mul, hc]⟩)

@[simp] theorem Vertex.act_mk (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    Vertex.act g (Vertex.mk R K L hL) = Vertex.mk R K (latticeMap g L) (hL.map g) :=
  rfl

theorem Vertex.act_one (v : Vertex R K) : Vertex.act 1 v = v := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_one L.1))

theorem Vertex.act_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) :
    Vertex.act (g * h) v = Vertex.act g (Vertex.act h v) := by
  induction v using Quotient.inductionOn with
  | h L => exact congrArg _ (Subtype.ext (latticeMap_mul g h L.1))

theorem eq_stdLattice_of_homothetic_of_le {L : Submodule R (Fin 2 → K)}
    (hhom : Homothetic (stdLattice R K) L) (hle : L ≤ stdLattice R K)
    {v : Fin 2 → K} (hv : v ∈ L) (hv0 : v 0 = 1) : L = stdLattice R K := by
  obtain ⟨c, rfl⟩ := hhom

  have hc : IsLocalization.IsInteger R ((c : K)) := by
    have h1 : (c : K) • (Pi.single 0 1 : Fin 2 → K) ∈
        latticeMap (scalarGL c) (stdLattice R K) :=
      mem_latticeMap_scalarGL.mpr ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, rfl⟩
    have h2 := hle h1 0
    rwa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2

  obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp hv
  have hcw : (c : K) * w 0 = 1 := by
    have h3 := congrFun hwv 0
    rw [Pi.smul_apply, smul_eq_mul] at h3
    rw [h3, hv0]
  have hcinv : IsLocalization.IsInteger R (((c⁻¹ : Kˣ) : K)) := by
    have h4 : ((c⁻¹ : Kˣ) : K) = w 0 := by
      calc ((c⁻¹ : Kˣ) : K) = ((c⁻¹ : Kˣ) : K) * ((c : K) * w 0) := by rw [hcw, mul_one]
        _ = (((c⁻¹ : Kˣ) : K) * (c : K)) * w 0 := by rw [mul_assoc]
        _ = w 0 := by rw [Units.inv_mul, one_mul]
    rw [h4]
    exact hw 0

  apply le_antisymm hle
  intro u hu
  rw [mem_latticeMap_scalarGL]
  refine ⟨((c⁻¹ : Kˣ) : K) • u, fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul]
    exact IsLocalization.isInteger_mul hcinv (hu i)
  · rw [smul_smul, Units.mul_inv, one_smul]

variable [IsFractionRing R K]

theorem latticeMap_stdLattice_eq_iff_mem_range (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeMap g (stdLattice R K) = stdLattice R K ↔
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hinjM : Function.Injective
      ((algebraMap R K).mapMatrix : Matrix (Fin 2) (Fin 2) R →+* Matrix (Fin 2) (Fin 2) K) :=
    fun M N h => by
      ext i j
      apply hinj
      have := congrArg (fun X => X i j) h
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using this
  constructor
  · intro hfix

    have hcol : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ (Pi.single j 1) ∈ stdLattice R K :=
        hfix ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this

    have hfix' : latticeMap g⁻¹ (stdLattice R K) = stdLattice R K := by
      conv_lhs => rw [← hfix, latticeMap_inv_latticeMap]
    have hcol' : ∀ i j,
        IsLocalization.IsInteger R (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) i j) := by
      intro i j
      have hj : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (Pi.single j 1) ∈ stdLattice R K :=
        hfix' ▸ mulVec_mem_latticeMap (single_one_mem_stdLattice R K j)
      have := hj i
      rwa [mulVec_single_one] at this

    choose a ha using fun p : Fin 2 × Fin 2 => hcol p.1 p.2
    choose b hb using fun p : Fin 2 × Fin 2 => hcol' p.1 p.2
    set A : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => a (i, j) with hA
    set B : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => b (i, j) with hB
    have hmapA : (algebraMap R K).mapMatrix A = (g : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact ha (i, j)
    have hmapB : (algebraMap R K).mapMatrix B =
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      exact hb (i, j)
    have hAB : A * B = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hBA : B * A = 1 := by
      apply hinjM
      rw [map_mul, map_one, hmapA, hmapB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    exact ha (i, j)
  · intro hg
    apply le_antisymm (latticeMap_le_stdLattice_of_isInteger
      (isInteger_apply_of_mem_range hg))

    have hg' : g⁻¹ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range :=
      Subgroup.inv_mem _ hg
    have h1 : latticeMap g⁻¹ (stdLattice R K) ≤ stdLattice R K :=
      latticeMap_le_stdLattice_of_isInteger (isInteger_apply_of_mem_range hg')
    intro v hv
    have hv' : v ∈ latticeMap g (latticeMap g⁻¹ (stdLattice R K)) := by
      rw [latticeMap_latticeMap_inv]
      exact hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap.mp hv'
    exact mulVec_mem_latticeMap (h1 hw)

theorem Vertex.act_stdVertex_eq_iff (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Vertex.act g (stdVertex R K) = stdVertex R K ↔
      ∃ c : Kˣ, scalarGL c * g ∈
        (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range := by
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (latticeMap_stdLattice_eq_iff_mem_range _).mp (by
      rw [latticeMap_mul]
      exact hc)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by
      rw [← latticeMap_mul]
      exact (latticeMap_stdLattice_eq_iff_mem_range _).mpr hc⟩

def unitOfNeZero {ϖ : R} (hϖ : ϖ ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap R K ϖ)
    (fun h => hϖ (IsFractionRing.injective R K (by rw [h, map_zero])))

@[simp] theorem unitOfNeZero_coe {ϖ : R} (hϖ : ϖ ≠ 0) :
    ((unitOfNeZero (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

theorem isUnit_of_algebraMap_mul_eq_one {ϖ : R} {w : K}
    (hw : IsLocalization.IsInteger R w) (h : algebraMap R K ϖ * w = 1) : IsUnit ϖ := by
  obtain ⟨r, rfl⟩ := hw
  rw [← map_mul] at h
  have h1 : ϖ * r = 1 := IsFractionRing.injective R K (by rw [h, map_one])
  exact ⟨⟨ϖ, r, h1, (mul_comm r ϖ).trans h1⟩, rfl⟩

theorem single_one_one_notMem_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    (Pi.single 1 1 : Fin 2 → K) ∉
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  rw [mem_latticeMap_diagSnd_stdLattice]
  rintro ⟨-, w, hw, hweq⟩
  rw [unitOfNeZero_coe, Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

theorem latticeMap_diagSnd_ne_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      stdLattice R K := fun h =>
  single_one_one_notMem_latticeMap_diagSnd hϖ (h ▸ single_one_mem_stdLattice R K 1)

theorem latticeMap_diagSnd_le_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ stdLattice R K := by
  intro v hv
  rw [mem_latticeMap_diagSnd_stdLattice] at hv
  obtain ⟨h0, w, hw, hw'⟩ := hv
  intro i
  fin_cases i
  · exact h0
  · show IsLocalization.IsInteger R (v 1)
    rw [← hw', unitOfNeZero_coe]
    exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw

theorem latticeMap_diagSnd_lt_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K :=
  lt_of_le_of_ne (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
    (latticeMap_diagSnd_ne_stdLattice hϖ)

theorem not_homothetic_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
  intro hhom
  exact latticeMap_diagSnd_ne_stdLattice hϖ
    (eq_stdLattice_of_homothetic_of_le hhom (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)
      (single_zero_one_mem_latticeMap_diagSnd _) (Pi.single_eq_same 0 1))

theorem stdVertex_ne_act_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd hϖ h.symm

def AdjacentLattice (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ (ϖ : R) (hϖ : Irreducible ϖ),
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) L < L' ∧ L' < L

theorem mem_latticeMap_scalarGL_stdLattice {ϖ : R} (hϖ : ϖ ≠ 0) {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ↔
      ∀ i, ∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K ϖ * w = v i := by
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    intro i
    exact ⟨w i, hw i, by rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]⟩
  · intro h
    choose w hw hw' using h
    refine ⟨w, hw, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, unitOfNeZero_coe]
    exact hw' i

theorem latticeMap_scalarGL_le_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≤
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at hv
  rw [mem_latticeMap_diagSnd_stdLattice]
  obtain ⟨w0, hw0, hw0'⟩ := hv 0
  obtain ⟨w1, hw1, hw1'⟩ := hv 1
  refine ⟨?_, w1, hw1, by rw [unitOfNeZero_coe]; exact hw1'⟩
  rw [← hw0']
  exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw0

theorem latticeMap_scalarGL_ne_latticeMap_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) ≠
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) := by
  intro h
  have he0 := single_zero_one_mem_latticeMap_diagSnd
    (R := R) (unitOfNeZero (K := K) hϖ.ne_zero)
  rw [← h, mem_latticeMap_scalarGL_stdLattice hϖ.ne_zero] at he0
  obtain ⟨w, hw, hweq⟩ := he0 0
  rw [Pi.single_eq_same] at hweq
  exact hϖ.not_isUnit (isUnit_of_algebraMap_mul_eq_one hw hweq)

theorem adjacentLattice_stdLattice_diagSnd {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) :=
  ⟨ϖ, hϖ,
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ),
    latticeMap_diagSnd_lt_stdLattice hϖ⟩

theorem adjacentLattice_diagSnd_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    AdjacentLattice
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  have h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) :=
    lt_of_le_of_ne (latticeMap_scalarGL_le_latticeMap_diagSnd hϖ)
      (latticeMap_scalarGL_ne_latticeMap_diagSnd hϖ)
  have h₂ : latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
      stdLattice R K := latticeMap_diagSnd_lt_stdLattice hϖ
  refine ⟨ϖ, hϖ, ?_, (latticeMap_lt_latticeMap_iff _).mpr h₂⟩
  have h₃ := (latticeMap_lt_latticeMap_iff
    (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))).mpr h₁
  rwa [← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul] at h₃

theorem latticeMap_diagSnd_sq_le_stdLattice {ϖ : R} (hϖ : Irreducible ϖ) :
    latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) ≤
      stdLattice R K :=
  le_trans (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero))
    (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero)

theorem not_homothetic_stdLattice_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ Homothetic (stdLattice R K)
      (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K))) := by
  intro hhom

  have he0 : (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    have h5 := mulVec_mem_latticeMap (g := diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
      (single_zero_one_mem_latticeMap_diagSnd (R := R)
        (unitOfNeZero (K := K) hϖ.ne_zero))
    have h6 : ((diagSnd (unitOfNeZero (K := K) hϖ.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (Pi.single 0 1 : Fin 2 → K) = (Pi.single 0 1 : Fin 2 → K) := by
      rw [diagSnd_mulVec]
      funext i
      fin_cases i <;> simp
    rwa [h6] at h5

  have heq := eq_stdLattice_of_homothetic_of_le hhom
    (latticeMap_diagSnd_sq_le_stdLattice hϖ) he0 (Pi.single_eq_same 0 1)
  have he1 : (Pi.single 1 1 : Fin 2 → K) ∈
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (latticeMap (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K)) := by
    rw [heq]
    exact single_one_mem_stdLattice R K 1
  exact single_one_one_notMem_latticeMap_diagSnd hϖ
    (latticeMap_mono _ (latticeMap_diagSnd_le_stdLattice hϖ.ne_zero) he1)

theorem stdVertex_ne_act_diagSnd_sq {ϖ : R} (hϖ : Irreducible ϖ) :
    Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero))
        (Vertex.act (diagSnd (unitOfNeZero (K := K) hϖ.ne_zero)) (stdVertex R K)) ≠
      stdVertex R K := by
  rw [stdVertex, Vertex.act_mk, Vertex.act_mk, Ne, Vertex.mk_eq_mk_iff]
  exact fun h => not_homothetic_stdLattice_diagSnd_sq hϖ h.symm

example : IsDiscreteValuationRing ℤ_[2] := inferInstance
example : IsFractionRing ℤ_[2] ℚ_[2] := inferInstance
example : Irreducible (2 : ℤ_[2]) := PadicInt.irreducible_p

example :
    Vertex.act (R := ℤ_[2]) (K := ℚ_[2])
        (diagSnd (unitOfNeZero (K := ℚ_[2]) (PadicInt.irreducible_p (p := 2)).ne_zero))
        (stdVertex ℤ_[2] ℚ_[2]) ≠
      stdVertex ℤ_[2] ℚ_[2] :=
  stdVertex_ne_act_diagSnd PadicInt.irreducible_p

end LT.LatticeTree

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

open Module
open scoped LinearAlgebra.Projectivization

section ResiduePlane

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem ne_bot_and_ne_top_iff_finrank_eq_one [FiniteDimensional k V]
    (hV : finrank k V = 2) (W : Submodule k V) :
    (W ≠ ⊥ ∧ W ≠ ⊤) ↔ finrank k W = 1 := by
  have hle : finrank k W ≤ 2 := hV ▸ W.finrank_le
  constructor
  · rintro ⟨hbot, htop⟩
    have h0 : finrank k W ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.mp h)
    have h2 : finrank k W ≠ 2 := fun h => htop (Submodule.eq_top_of_finrank_eq (h.trans hV.symm))
    omega
  · intro h1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, finrank_bot] at h1; exact absurd h1 (by norm_num)
    · rw [h, finrank_top, hV] at h1; exact absurd h1 (by norm_num)

set_option maxHeartbeats 800000 in

noncomputable def submoduleNeBotNeTopEquivProjectivization [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} ≃ ℙ k V :=
  (Equiv.subtypeEquivRight (ne_bot_and_ne_top_iff_finrank_eq_one hV)).trans
    (Projectivization.equivSubmodule k V).symm

set_option maxHeartbeats 800000 in

theorem card_submodule_ne_bot_ne_top_of_finrank_two [Finite k] [FiniteDimensional k V]
    (hV : finrank k V = 2) :
    Nat.card {W : Submodule k V // W ≠ ⊥ ∧ W ≠ ⊤} = Nat.card k + 1 :=
  (Nat.card_congr (submoduleNeBotNeTopEquivProjectivization hV)).trans
    (Projectivization.card_of_finrank_two k V hV)

end ResiduePlane

section NeighbourFamily

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem isInteger_neg {a : K} (ha : IsLocalization.IsInteger R a) :
    IsLocalization.IsInteger R (-a) := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨-a', map_neg _ _⟩

theorem isInteger_sub {a b : K} (ha : IsLocalization.IsInteger R a)
    (hb : IsLocalization.IsInteger R b) : IsLocalization.IsInteger R (a - b) := by
  rw [sub_eq_add_neg]
  exact IsLocalization.isInteger_add ha (isInteger_neg hb)

variable (R K) in

def interLattice (ϖ c d : R) : Submodule R (Fin 2 → K) where
  carrier := {v | (∀ i, IsLocalization.IsInteger R (v i)) ∧
    ∃ w : K, IsLocalization.IsInteger R w ∧
      algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w}
  add_mem' := by
    rintro v u ⟨hv, wv, hwv, hv'⟩ ⟨hu, wu, hwu, hu'⟩
    refine ⟨fun i => IsLocalization.isInteger_add (hv i) (hu i),
      wv + wu, IsLocalization.isInteger_add hwv hwu, ?_⟩
    simp only [Pi.add_apply]
    linear_combination hv' + hu'
  zero_mem' := by
    refine ⟨fun _ => IsLocalization.isInteger_zero, 0, IsLocalization.isInteger_zero, ?_⟩
    simp
  smul_mem' := by
    rintro r v ⟨hv, w, hw, hv'⟩
    refine ⟨fun i => by rw [Pi.smul_apply]; exact IsLocalization.isInteger_smul (hv i),
      r • w, IsLocalization.isInteger_smul hw, ?_⟩
    simp only [Pi.smul_apply, Algebra.smul_def]
    linear_combination algebraMap R K r * hv'

theorem mem_interLattice {ϖ c d : R} {v : Fin 2 → K} :
    v ∈ interLattice R K ϖ c d ↔
      (∀ i, IsLocalization.IsInteger R (v i)) ∧
        ∃ w : K, IsLocalization.IsInteger R w ∧
          algebraMap R K d * v 0 - algebraMap R K c * v 1 = algebraMap R K ϖ * w :=
  Iff.rfl

theorem interLattice_le_stdLattice (ϖ c d : R) :
    interLattice R K ϖ c d ≤ stdLattice R K :=
  fun _ hv => hv.1

variable (R K) in

def vecPair (c d : R) : Fin 2 → K := ![algebraMap R K c, algebraMap R K d]

@[simp] theorem vecPair_zero (c d : R) : vecPair R K c d 0 = algebraMap R K c := rfl

@[simp] theorem vecPair_one (c d : R) : vecPair R K c d 1 = algebraMap R K d := rfl

theorem vecPair_mem_stdLattice (c d : R) : vecPair R K c d ∈ stdLattice R K := by
  intro i
  fin_cases i
  · exact ⟨c, rfl⟩
  · exact ⟨d, rfl⟩

theorem vecPair_mem_interLattice (ϖ c d : R) :
    vecPair R K c d ∈ interLattice R K ϖ c d := by
  refine ⟨vecPair_mem_stdLattice c d, 0, IsLocalization.isInteger_zero, ?_⟩
  simp [mul_comm]

variable [IsFractionRing R K]

theorem exists_isInteger_eq_algebraMap_mul_iff_dvd {ϖ x : R} :
    (∃ w : K, IsLocalization.IsInteger R w ∧ algebraMap R K x = algebraMap R K ϖ * w) ↔
      ϖ ∣ x := by
  constructor
  · rintro ⟨w, ⟨w', rfl⟩, hw⟩
    rw [← map_mul] at hw
    exact ⟨w', IsFractionRing.injective R K hw⟩
  · rintro ⟨y, rfl⟩
    exact ⟨algebraMap R K y, ⟨y, rfl⟩, by rw [map_mul]⟩

theorem vecPair_mem_interLattice_iff_dvd {ϖ c d x y : R} :
    vecPair R K x y ∈ interLattice R K ϖ c d ↔ ϖ ∣ d * x - c * y := by
  rw [mem_interLattice]
  constructor
  · rintro ⟨-, w, hw, hweq⟩
    refine exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w, hw, ?_⟩
    rw [map_sub, map_mul, map_mul, ← vecPair_zero (K := K) x y, ← vecPair_one (K := K) x y]
    exact hweq
  · intro hdvd
    obtain ⟨w, hw, hweq⟩ := exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K).mpr hdvd
    refine ⟨vecPair_mem_stdLattice x y, w, hw, ?_⟩
    rw [vecPair_zero, vecPair_one, ← hweq, map_sub, map_mul, map_mul]

theorem dvd_of_interLattice_eq {ϖ c d c' d' : R}
    (h : interLattice R K ϖ c d = interLattice R K ϖ c' d') :
    ϖ ∣ d' * c - c' * d := by
  have hmem := vecPair_mem_interLattice (R := R) (K := K) ϖ c d
  rw [h, vecPair_mem_interLattice_iff_dvd] at hmem
  exact hmem

omit [IsFractionRing R K] in

theorem interLattice_one_eq_of_dvd_sub {ϖ a a' : R} (h : ϖ ∣ a - a') :
    interLattice R K ϖ 1 a = interLattice R K ϖ 1 a' := by
  have key : ∀ {b b' : R}, ϖ ∣ b - b' →
      interLattice R K ϖ 1 b ≤ interLattice R K ϖ 1 b' := by
    rintro b b' ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r, hr⟩ := hv 0
    refine ⟨hv, w - algebraMap R K (y * r), isInteger_sub hw ⟨y * r, rfl⟩, ?_⟩
    have hb : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [hb]
    simp only [map_mul, map_one, one_mul] at hweq ⊢
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr
  exact le_antisymm (key h) (key (dvd_sub_comm.mp h))

theorem latticeMap_scalarGL_le_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) (c d : R) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤
      interLattice R K ϖ c d := by
  intro v hv
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at hv
  choose w hw hw' using hv
  refine ⟨fun i => by rw [← hw' i]; exact IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ (hw i),
    algebraMap R K d * w 0 - algebraMap R K c * w 1,
    isInteger_sub (IsLocalization.isInteger_mul ⟨d, rfl⟩ (hw 0))
      (IsLocalization.isInteger_mul ⟨c, rfl⟩ (hw 1)),
    by rw [← hw' 0, ← hw' 1]; ring⟩

theorem dvd_of_vecPair_mem_latticeMap_scalarGL {ϖ : R} (hϖ : ϖ ≠ 0) {x y : R}
    (h : vecPair R K x y ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :
    ϖ ∣ x ∧ ϖ ∣ y := by
  rw [mem_latticeMap_scalarGL_stdLattice hϖ] at h
  obtain ⟨w0, hw0, hw0'⟩ := h 0
  obtain ⟨w1, hw1, hw1'⟩ := h 1
  rw [vecPair_zero] at hw0'
  rw [vecPair_one] at hw1'
  exact ⟨exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w0, hw0, hw0'.symm⟩,
    exists_isInteger_eq_algebraMap_mul_iff_dvd.mp ⟨w1, hw1, hw1'.symm⟩⟩

theorem latticeMap_scalarGL_lt_interLattice {ϖ : R} (hϖ : ϖ ≠ 0) {c d : R}
    (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) <
      interLattice R K ϖ c d := by
  refine lt_of_le_of_ne (latticeMap_scalarGL_le_interLattice hϖ c d) (fun h => hcd ?_)
  exact dvd_of_vecPair_mem_latticeMap_scalarGL hϖ
    (h ▸ vecPair_mem_interLattice (R := R) (K := K) ϖ c d)

theorem interLattice_lt_stdLattice {ϖ : R} {c d : R} (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d)) :
    interLattice R K ϖ c d < stdLattice R K := by
  rw [lt_iff_le_and_ne]
  refine ⟨interLattice_le_stdLattice ϖ c d, fun h => ?_⟩
  rcases not_and_or.mp hcd with hc | hd
  ·
    have he : vecPair R K 0 1 ∈ stdLattice R K := vecPair_mem_stdLattice 0 1
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, zero_sub] at he
    exact hc (dvd_neg.mp he)
  ·
    have he : vecPair R K 1 0 ∈ stdLattice R K := vecPair_mem_stdLattice 1 0
    rw [← h, vecPair_mem_interLattice_iff_dvd] at he
    rw [mul_zero, mul_one, sub_zero] at he
    exact hd he

variable (R K) in

noncomputable def neighborOfOption (ϖ : R) (x : Option (R ⧸ Ideal.span {ϖ})) :
    Submodule R (Fin 2 → K) :=
  x.elim (interLattice R K ϖ 0 1) (fun y => interLattice R K ϖ 1 y.out)

theorem neighborOfOption_mem_interval {ϖ : R} (hϖ : Irreducible ϖ)
    (x : Option (R ⧸ Ideal.span {ϖ})) :
    latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) <
        neighborOfOption R K ϖ x ∧
      neighborOfOption R K ϖ x < stdLattice R K := by
  have hcd : ∀ y : R, ¬(ϖ ∣ (1 : R) ∧ ϖ ∣ y) := fun y h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.1)
  have hcd' : ¬(ϖ ∣ (0 : R) ∧ ϖ ∣ (1 : R)) := fun h =>
    hϖ.not_isUnit (isUnit_of_dvd_one h.2)
  cases x with
  | none => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd',
      interLattice_lt_stdLattice hcd'⟩
  | some y => exact ⟨latticeMap_scalarGL_lt_interLattice hϖ.ne_zero (hcd _),
      interLattice_lt_stdLattice (hcd _)⟩

theorem neighborOfOption_injective {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (neighborOfOption R K ϖ) := by
  have haff : ∀ (a : R), interLattice R K ϖ 0 1 ≠ interLattice R K ϖ 1 a := by
    intro a h
    have := dvd_of_interLattice_eq h
    rw [mul_zero, one_mul, zero_sub] at this
    exact hϖ.not_isUnit (isUnit_of_dvd_one (dvd_neg.mp this))
  rintro (_ | a) (_ | b) h
  · rfl
  · exact absurd h (haff _)
  · exact absurd h.symm (haff _)
  · have hd := dvd_of_interLattice_eq h
    rw [mul_one, one_mul] at hd
    rw [Option.some.injEq, ← Ideal.Quotient.mk_out a, ← Ideal.Quotient.mk_out b,
      Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.mpr (dvd_sub_comm.mp hd)

theorem neighborOfOption_injective_into_interval {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Injective (fun x : Option (R ⧸ Ideal.span {ϖ}) =>
      (⟨neighborOfOption R K ϖ x, neighborOfOption_mem_interval hϖ x⟩ :
        {L : Submodule R (Fin 2 → K) //
          latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < L ∧
            L < stdLattice R K})) :=
  fun _ _ h => neighborOfOption_injective hϖ (congrArg Subtype.val h)

theorem card_option_quotient (ϖ : R) [Finite (R ⧸ Ideal.span {ϖ})] :
    Nat.card (Option (R ⧸ Ideal.span {ϖ})) = Nat.card (R ⧸ Ideal.span {ϖ}) + 1 :=
  Finite.card_option

end NeighbourFamily

section Gates

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem interLattice_zero_zero (ϖ : R) : interLattice R K ϖ 0 0 = stdLattice R K := by
  refine le_antisymm (interLattice_le_stdLattice ϖ 0 0) (fun v hv => ?_)
  exact ⟨hv, 0, IsLocalization.isInteger_zero, by simp⟩

variable [IsFractionRing R K]

theorem interLattice_one_zero {ϖ : R} (hϖ : ϖ ≠ 0) :
    interLattice R K ϖ 1 0 =
      latticeMap (diagSnd (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  ext v
  rw [mem_interLattice, mem_latticeMap_diagSnd_stdLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    rw [map_zero, zero_mul, map_one, one_mul, zero_sub] at hweq
    refine ⟨hv 0, -w, isInteger_neg hw, ?_⟩
    rw [unitOfNeZero_coe, mul_neg, ← hweq, neg_neg]
  · rintro ⟨h0, w, hw, hweq⟩
    rw [unitOfNeZero_coe] at hweq
    refine ⟨fun i => ?_, -w, isInteger_neg hw, ?_⟩
    · fin_cases i
      · exact h0
      · exact hweq ▸ IsLocalization.isInteger_mul ⟨ϖ, rfl⟩ hw
    · rw [map_zero, zero_mul, map_one, one_mul, zero_sub, ← hweq, mul_neg]

end Gates

section PadicGates

example : interLattice ℤ_[2] ℚ_[2] 2 1 0 ≠ interLattice ℤ_[2] ℚ_[2] 2 1 1 := by
  intro h
  have hd := dvd_of_interLattice_eq h
  rw [mul_one, one_mul, sub_zero] at hd
  exact (PadicInt.irreducible_p (p := 2)).not_isUnit (isUnit_of_dvd_one hd)

example : interLattice ℤ_[2] ℚ_[2] 2 0 1 ≠ interLattice ℤ_[2] ℚ_[2] 2 1 0 := by
  intro h
  have hd := dvd_of_interLattice_eq h
  rw [mul_zero, one_mul, zero_sub] at hd
  exact (PadicInt.irreducible_p (p := 2)).not_isUnit
    (isUnit_of_dvd_one (dvd_neg.mp hd))

example : interLattice ℤ_[2] ℚ_[2] 2 1 0 = interLattice ℤ_[2] ℚ_[2] 2 1 2 :=
  interLattice_one_eq_of_dvd_sub ⟨-1, by ring⟩

example (x : Option (ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])})) :
    neighborOfOption ℤ_[2] ℚ_[2] 2 x < stdLattice ℤ_[2] ℚ_[2] :=
  (neighborOfOption_mem_interval PadicInt.irreducible_p x).2

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

structure IntegralAut (R K : Type*) [CommRing R] [Field K] [Algebra R K] where

  toField : K ≃+* K

  toBase : R ≃+* R

  commutes : ∀ r : R, toField (algebraMap R K r) = algebraMap R K (toBase r)

namespace IntegralAut

variable (R K) in

def refl : IntegralAut R K where
  toField := RingEquiv.refl K
  toBase := RingEquiv.refl R
  commutes _ := rfl

@[simp] theorem refl_toField : (refl R K).toField = RingEquiv.refl K := rfl

@[simp] theorem refl_toBase : (refl R K).toBase = RingEquiv.refl R := rfl

def comp (σ τ : IntegralAut R K) : IntegralAut R K where
  toField := τ.toField.trans σ.toField
  toBase := τ.toBase.trans σ.toBase
  commutes r := by
    show σ.toField (τ.toField (algebraMap R K r)) = algebraMap R K (σ.toBase (τ.toBase r))
    rw [τ.commutes, σ.commutes]

@[simp] theorem comp_toField_apply (σ τ : IntegralAut R K) (x : K) :
    (σ.comp τ).toField x = σ.toField (τ.toField x) := rfl

@[simp] theorem comp_toBase_apply (σ τ : IntegralAut R K) (r : R) :
    (σ.comp τ).toBase r = σ.toBase (τ.toBase r) := rfl

theorem symm_commutes (σ : IntegralAut R K) (r : R) :
    σ.toField.symm (algebraMap R K r) = algebraMap R K (σ.toBase.symm r) := by
  apply σ.toField.injective
  rw [RingEquiv.apply_symm_apply, σ.commutes, RingEquiv.apply_symm_apply]

def symm (σ : IntegralAut R K) : IntegralAut R K where
  toField := σ.toField.symm
  toBase := σ.toBase.symm
  commutes := σ.symm_commutes

theorem symm_toField (σ : IntegralAut R K) : σ.symm.toField = σ.toField.symm := rfl

attribute [local simp] symm_toField
theorem symm_toBase (σ : IntegralAut R K) : σ.symm.toBase = σ.toBase.symm := rfl

attribute [local simp] symm_toBase
theorem isInteger_map (σ : IntegralAut R K) {x : K}
    (hx : IsLocalization.IsInteger R x) : IsLocalization.IsInteger R (σ.toField x) := by
  obtain ⟨r, rfl⟩ := hx
  exact ⟨σ.toBase r, (σ.commutes r).symm⟩

def mapGL (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K :=
  Matrix.GeneralLinearGroup.map (σ.toField : K →+* K)

theorem mapGL_apply (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (i j : Fin 2) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      σ.toField ((g : Matrix (Fin 2) (Fin 2) K) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

theorem mapGL_coe (σ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    ((σ.mapGL g : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((g : Matrix (Fin 2) (Fin 2) K)).map (σ.toField : K →+* K) := by
  ext i j
  rw [mapGL_apply, Matrix.map_apply]
  rfl

theorem mapGL_comp (σ τ : IntegralAut R K) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (σ.comp τ).mapGL g = σ.mapGL (τ.mapGL g) := by
  ext i j
  rw [mapGL_apply, mapGL_apply, mapGL_apply, comp_toField_apply]

theorem mapGL_refl (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (refl R K).mapGL g = g := by
  ext i j
  rw [mapGL_apply]
  rfl

def unitMap (σ : IntegralAut R K) (c : Kˣ) : Kˣ where
  val := σ.toField c
  inv := σ.toField ↑c⁻¹
  val_inv := by rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by rw [← map_mul, Units.inv_mul, map_one]

@[simp] theorem unitMap_coe (σ : IntegralAut R K) (c : Kˣ) :
    ((σ.unitMap c : Kˣ) : K) = σ.toField c := rfl

end IntegralAut

attribute [local simp] IntegralAut.symm_toField IntegralAut.symm_toBase

def galVec (σ : IntegralAut R K) (v : Fin 2 → K) : Fin 2 → K :=
  fun i => σ.toField (v i)

@[simp] theorem galVec_apply (σ : IntegralAut R K) (v : Fin 2 → K) (i : Fin 2) :
    galVec σ v i = σ.toField (v i) := rfl

theorem galVec_add (σ : IntegralAut R K) (v w : Fin 2 → K) :
    galVec σ (v + w) = galVec σ v + galVec σ w := by
  funext i
  simp [galVec, map_add]

theorem galVec_zero (σ : IntegralAut R K) : galVec σ (0 : Fin 2 → K) = 0 := by
  funext i
  simp [galVec]

theorem galVec_smul (σ : IntegralAut R K) (r : R) (v : Fin 2 → K) :
    galVec σ (r • v) = σ.toBase r • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, Algebra.smul_def,
    Algebra.smul_def, map_mul, σ.commutes]

theorem galVec_smul_field (σ : IntegralAut R K) (c : K) (v : Fin 2 → K) :
    galVec σ (c • v) = σ.toField c • galVec σ v := by
  funext i
  rw [galVec_apply, Pi.smul_apply, Pi.smul_apply, galVec_apply, smul_eq_mul, smul_eq_mul,
    map_mul]

theorem galVec_galVec (σ τ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec τ v) = galVec (σ.comp τ) v := rfl

@[simp] theorem galVec_refl (v : Fin 2 → K) : galVec (IntegralAut.refl R K) v = v := rfl

theorem galVec_symm_galVec (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ.symm (galVec σ v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_symm_galVec
theorem galVec_galVec_symm (σ : IntegralAut R K) (v : Fin 2 → K) :
    galVec σ (galVec σ.symm v) = v := by
  funext i
  simp [galVec]

attribute [local simp] galVec_galVec_symm
theorem galVec_mulVec (σ : IntegralAut R K) (M : Matrix (Fin 2) (Fin 2) K)
    (v : Fin 2 → K) :
    galVec σ (M *ᵥ v) = (M.map (σ.toField : K →+* K)) *ᵥ galVec σ v := by
  funext i
  rw [galVec_apply]
  exact RingHom.map_mulVec (σ.toField : K →+* K) M v i

def latticeGal (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) where
  carrier := galVec σ '' L
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, L.add_mem hv hw, galVec_add σ v w⟩
  zero_mem' := ⟨0, L.zero_mem, galVec_zero σ⟩
  smul_mem' := by
    rintro r _ ⟨w, hw, rfl⟩
    refine ⟨σ.toBase.symm r • w, L.smul_mem _ hw, ?_⟩
    rw [galVec_smul, RingEquiv.apply_symm_apply]

theorem mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {v : Fin 2 → K} : v ∈ latticeGal σ L ↔ ∃ w ∈ L, galVec σ w = v := Iff.rfl

theorem galVec_mem_latticeGal {σ : IntegralAut R K} {L : Submodule R (Fin 2 → K)}
    {w : Fin 2 → K} (hw : w ∈ L) : galVec σ w ∈ latticeGal σ L :=
  ⟨w, hw, rfl⟩

@[simp] theorem latticeGal_refl (L : Submodule R (Fin 2 → K)) :
    latticeGal (IntegralAut.refl R K) L = L := by
  ext v
  exact ⟨fun ⟨w, hw, h⟩ => h ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩

theorem latticeGal_comp (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    latticeGal (σ.comp τ) L = latticeGal σ (latticeGal τ L) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨galVec τ w, galVec_mem_latticeGal hw, rfl⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩

theorem latticeGal_symm_latticeGal (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ.symm (latticeGal σ L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_symm_galVec]
  · intro hv
    exact ⟨galVec σ v, galVec_mem_latticeGal hv, galVec_symm_galVec σ v⟩

attribute [local simp] latticeGal_symm_latticeGal
theorem latticeGal_latticeGal_symm (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : latticeGal σ (latticeGal σ.symm L) = L := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    rwa [galVec_galVec_symm]
  · intro hv
    exact ⟨galVec σ.symm v, galVec_mem_latticeGal hv, galVec_galVec_symm σ v⟩

attribute [local simp] latticeGal_latticeGal_symm
theorem latticeGal_injective (σ : IntegralAut R K) :
    Function.Injective (latticeGal (R := R) (K := K) σ) :=
  Function.LeftInverse.injective (latticeGal_symm_latticeGal σ)

theorem latticeGal_span (σ : IntegralAut R K) (s : Set (Fin 2 → K)) :
    latticeGal σ (Submodule.span R s) = Submodule.span R (galVec σ '' s) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    induction hw using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => rw [galVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [galVec_smul]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact galVec_mem_latticeGal (Submodule.subset_span hx)

theorem latticeGal_stdLattice (σ : IntegralAut R K) :
    latticeGal σ (stdLattice R K) = stdLattice R K := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    intro i
    exact σ.isInteger_map (hw i)
  · intro v hv
    refine ⟨galVec σ.symm v, fun i => ?_, galVec_galVec_symm σ v⟩
    exact σ.symm.isInteger_map (hv i)

theorem latticeGal_latticeMap (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap g L) = latticeMap (σ.mapGL g) (latticeGal σ L) := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨galVec σ w, galVec_mem_latticeGal hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨(g : Matrix (Fin 2) (Fin 2) K) *ᵥ w, mulVec_mem_latticeMap hw, ?_⟩
    simp only [mulVecLinR_apply]
    rw [galVec_mulVec, σ.mapGL_coe]

theorem latticeGal_latticeMap_stdLattice (σ : IntegralAut R K)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    latticeGal σ (latticeMap g (stdLattice R K)) =
      latticeMap (σ.mapGL g) (stdLattice R K) := by
  rw [latticeGal_latticeMap, latticeGal_stdLattice]

theorem mapGL_scalarGL (σ : IntegralAut R K) (c : Kˣ) :
    σ.mapGL (scalarGL c) = scalarGL (σ.unitMap c) := by
  ext i j
  rw [σ.mapGL_apply, scalarGL_coe, scalarGL_coe, Matrix.smul_apply, Matrix.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, IntegralAut.unitMap_coe]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, map_zero]

theorem latticeGal_scalarGL (σ : IntegralAut R K) (c : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeGal σ (latticeMap (scalarGL c) L) =
      latticeMap (scalarGL (σ.unitMap c)) (latticeGal σ L) := by
  rw [latticeGal_latticeMap, mapGL_scalarGL]

theorem IsFullLattice.gal {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (σ : IntegralAut R K) : IsFullLattice (latticeGal σ L) := by
  obtain ⟨hfg, hspan⟩ := hL
  constructor
  · obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp hfg
    exact Submodule.fg_def.mpr
      ⟨galVec σ '' S, hSfin.image _, by rw [← latticeGal_span, hS]⟩
  · rw [eq_top_iff]
    intro v _
    have hv : galVec σ.symm v ∈ Submodule.span K (L : Set (Fin 2 → K)) :=
      hspan ▸ Submodule.mem_top
    have hkey : ∀ w ∈ Submodule.span K (L : Set (Fin 2 → K)),
        galVec σ w ∈ Submodule.span K ((latticeGal σ L : Set (Fin 2 → K))) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (galVec_mem_latticeGal hx)
      | zero => rw [galVec_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [galVec_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [galVec_smul_field]; exact Submodule.smul_mem _ _ hx
    have := hkey _ hv
    rwa [galVec_galVec_symm] at this

def Vertex.galAct (σ : IntegralAut R K) : Vertex R K → Vertex R K :=
  Quotient.map (fun L => ⟨latticeGal σ L.1, L.2.gal σ⟩)
    (by
      rintro ⟨L, hL⟩ ⟨L', hL'⟩ ⟨c, hc⟩
      refine ⟨σ.unitMap c, ?_⟩
      show latticeMap _ (latticeGal σ L) = latticeGal σ L'
      rw [← latticeGal_scalarGL, hc])

@[simp] theorem Vertex.galAct_mk (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K))
    (hL : IsFullLattice L) :
    Vertex.galAct σ (Vertex.mk R K L hL) = Vertex.mk R K (latticeGal σ L) (hL.gal σ) :=
  rfl

theorem Vertex.galAct_stdVertex (σ : IntegralAut R K) :
    Vertex.galAct σ (stdVertex R K) = stdVertex R K := by
  rw [stdVertex, Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_stdLattice]
  exact Homothetic.refl _

def twistedLatticeMap (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (L : Submodule R (Fin 2 → K)) : Submodule R (Fin 2 → K) :=
  latticeMap δ (latticeGal σ L)

theorem twistedLatticeMap_twistedLatticeMap (δ δ' : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ τ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ' τ L) =
      twistedLatticeMap (δ * σ.mapGL δ') (σ.comp τ) L := by
  unfold twistedLatticeMap
  rw [latticeGal_latticeMap, ← latticeMap_mul, latticeGal_comp]

def normTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ

def normThree (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K) :
    Matrix.GeneralLinearGroup (Fin 2) K :=
  δ * σ.mapGL δ * (σ.comp σ).mapGL δ

theorem twistedLatticeMap_two_of_orderTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : σ.comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ L) = latticeMap (normTwo δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normTwo
  rw [latticeGal_refl]

theorem twistedLatticeMap_three_of_orderThree (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ (twistedLatticeMap δ σ L)) =
      latticeMap (normThree δ σ) L := by
  rw [twistedLatticeMap_twistedLatticeMap, twistedLatticeMap_twistedLatticeMap, hσ]
  unfold twistedLatticeMap normThree
  rw [latticeGal_refl]

theorem latticeMap_norm_eq_self_of_twisted_fixed (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    {L : Submodule R (Fin 2 → K)} (hL : twistedLatticeMap δ σ L = L) :
    latticeMap (normThree δ σ) L = L := by
  rw [← twistedLatticeMap_three_of_orderThree δ hσ, hL, hL, hL]

theorem complex_I_ne_neg_I : Complex.I ≠ -Complex.I := by
  intro h
  have h2 : Complex.I.im = (-Complex.I).im := congrArg Complex.im h
  rw [Complex.neg_im, Complex.I_im] at h2
  norm_num at h2

def conjAut : IntegralAut ℂ ℂ where
  toField := starRingAut
  toBase := starRingAut
  commutes r := by
    simp [Algebra.algebraMap_self]

theorem conjAut_toField_ne_refl : conjAut.toField ≠ RingEquiv.refl ℂ := by
  intro h
  have hI : conjAut.toField Complex.I = Complex.I := by rw [h]; rfl
  have hI' : conjAut.toField Complex.I = -Complex.I := Complex.conj_I
  rw [hI'] at hI
  exact complex_I_ne_neg_I hI.symm

theorem galVec_conjAut_ne : galVec conjAut ![1, Complex.I] ≠ ![1, Complex.I] := by
  intro h
  have h1 : conjAut.toField (![1, Complex.I] 1) = ![1, Complex.I] 1 := congrFun h 1
  have h2 : (![1, Complex.I] 1 : ℂ) = Complex.I := by simp
  rw [h2] at h1
  rw [show conjAut.toField Complex.I = -Complex.I from Complex.conj_I] at h1
  exact complex_I_ne_neg_I h1.symm

theorem latticeGal_conj_line_ne :
    latticeGal conjAut (Submodule.span ℂ {![1, Complex.I]}) ≠
      Submodule.span ℂ {![1, Complex.I]} := by
  intro h

  have hmem : galVec conjAut ![1, Complex.I] ∈
      Submodule.span ℂ {![(1 : ℂ), Complex.I]} := by
    rw [← h]
    exact galVec_mem_latticeGal (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem

  have h0 : c * 1 = 1 := by
    have := congrFun hc 0
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul] using this

  have h1 : c * Complex.I = -Complex.I := by
    have := congrFun hc 1
    simpa [galVec, conjAut, Pi.smul_apply, smul_eq_mul, Complex.conj_I] using this
  rw [mul_one] at h0
  rw [h0, one_mul] at h1
  exact complex_I_ne_neg_I h1

theorem conjAut_comp_conjAut : conjAut.comp conjAut = IntegralAut.refl ℂ ℂ := by
  unfold conjAut IntegralAut.comp IntegralAut.refl
  congr 1 <;>
  · ext x
    exact star_star x

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℂ) (L : Submodule ℂ (Fin 2 → ℂ)) :
    twistedLatticeMap δ conjAut (twistedLatticeMap δ conjAut L) =
      latticeMap (normTwo δ conjAut) L :=
  twistedLatticeMap_two_of_orderTwo δ conjAut_comp_conjAut L

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def IsFixedVertex (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Vertex R K) : Prop :=
  Vertex.act g v = v

def fixedVertexSet (g : Matrix.GeneralLinearGroup (Fin 2) K) : Set (Vertex R K) :=
  {v | IsFixedVertex g v}

theorem mem_fixedVertexSet {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {v : Vertex R K} : v ∈ fixedVertexSet (R := R) g ↔ Vertex.act g v = v :=
  Iff.rfl

attribute [local simp] mem_fixedVertexSet
variable (R) in

noncomputable def unitOrbitalCount (g : Matrix.GeneralLinearGroup (Fin 2) K) : ℕ :=
  Nat.card (fixedVertexSet (R := R) g)

theorem isFixedVertex_mk_iff {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : IsFullLattice L} :
    IsFixedVertex g (Vertex.mk R K L hL) ↔ Homothetic (latticeMap g L) L := by
  rw [IsFixedVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]

theorem isFixedVertex_mk_of_latticeMap_eq {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {hL : IsFullLattice L}
    (h : latticeMap g L = L) : IsFixedVertex g (Vertex.mk R K L hL) :=
  isFixedVertex_mk_iff.mpr (by rw [h]; exact Homothetic.refl L)

theorem isFixedVertex_conj_iff (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    IsFixedVertex (h * g * h⁻¹) v ↔ IsFixedVertex g (Vertex.act h⁻¹ v) := by
  unfold IsFixedVertex
  rw [Vertex.act_mul, Vertex.act_mul]
  constructor
  · intro hfix
    have h2 := congrArg (Vertex.act h⁻¹) hfix
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one] at h2
  · intro hfix
    rw [hfix, ← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]

theorem fixedVertexSet_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    fixedVertexSet (R := R) (h * g * h⁻¹) = Vertex.act h '' fixedVertexSet (R := R) g := by
  ext v
  constructor
  · intro hv
    exact ⟨Vertex.act h⁻¹ v, (isFixedVertex_conj_iff g h v).mp hv, by
      rw [← Vertex.act_mul, mul_inv_cancel, Vertex.act_one]⟩
  · rintro ⟨w, hw, rfl⟩
    refine (isFixedVertex_conj_iff g h _).mpr ?_
    show IsFixedVertex g (Vertex.act h⁻¹ (Vertex.act h w))
    rwa [← Vertex.act_mul, inv_mul_cancel, Vertex.act_one]

theorem unitOrbitalCount_conj (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    unitOrbitalCount R (h * g * h⁻¹) = unitOrbitalCount R g := by
  rw [unitOrbitalCount, unitOrbitalCount, fixedVertexSet_conj]
  have hinj : Function.Injective (Vertex.act (R := R) h) := fun v w hvw => by
    have h2 := congrArg (Vertex.act h⁻¹) hvw
    rwa [← Vertex.act_mul, ← Vertex.act_mul, inv_mul_cancel, Vertex.act_one,
      Vertex.act_one] at h2
  exact Nat.card_congr (Equiv.Set.image _ _ hinj).symm

theorem isFixedVertex_scalarGL (c : Kˣ) (v : Vertex R K) :
    IsFixedVertex (scalarGL c) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.act (scalarGL c) (Vertex.mk R K L.1 L.2) = Vertex.mk R K L.1 L.2
    rw [Vertex.act_mk, Vertex.mk_eq_mk_iff]
    exact Homothetic.symm ⟨c, rfl⟩

theorem fixedVertexSet_scalarGL (c : Kˣ) :
    fixedVertexSet (R := R) (scalarGL c) = Set.univ :=
  Set.eq_univ_of_forall (isFixedVertex_scalarGL c)

theorem not_subsingleton_fixedVertexSet_scalarGL [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) (c : Kˣ) :
    ¬ (fixedVertexSet (R := R) (scalarGL c)).Subsingleton := by
  intro hsub
  exact stdVertex_ne_act_diagSnd (K := K) hϖ
    (hsub (isFixedVertex_scalarGL c _) (isFixedVertex_scalarGL c _)).symm

theorem isFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    IsFixedVertex g (stdVertex R K) :=
  (Vertex.act_stdVertex_eq_iff g).mpr ⟨1, by rwa [scalarGL_one, one_mul]⟩

theorem nonempty_fixedVertexSet_of_mem_range [IsFractionRing R K]
    {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range) :
    (fixedVertexSet (R := R) g).Nonempty :=
  ⟨stdVertex R K, isFixedVertex_stdVertex_of_mem_range hg⟩

section Engine

variable [IsFractionRing R K]

def mulVecPair (M : Matrix (Fin 2) (Fin 2) R) (c d : R) : Fin 2 → R :=
  M *ᵥ ![c, d]

@[simp] theorem mulVecPair_zero (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 0 = M 0 0 * c + M 0 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[simp] theorem mulVecPair_one (M : Matrix (Fin 2) (Fin 2) R) (c d : R) :
    mulVecPair M c d 1 = M 1 0 * c + M 1 1 * d := by
  simp [mulVecPair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVecPair_mul (M N : Matrix (Fin 2) (Fin 2) R) (c d : R) (i : Fin 2) :
    mulVecPair (M * N) c d i =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) i := by
  have h0 : mulVecPair (M * N) c d 0 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 0 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have h1 : mulVecPair (M * N) c d 1 =
      mulVecPair M (mulVecPair N c d 0) (mulVecPair N c d 1) 1 := by
    simp only [mulVecPair_zero, mulVecPair_one, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  fin_cases i
  · exact h0
  · exact h1

omit [IsFractionRing R K] in

theorem map_coe_apply (M : Matrix.GeneralLinearGroup (Fin 2) R) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (algebraMap R K) M :
        Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j =
      algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i j) :=
  Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j M

omit [IsFractionRing R K] in

theorem latticeMap_map_interLattice_le (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) ≤
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  rintro _ ⟨w, hwmem, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hwmem

  have hcoord : ∀ i : Fin 2,
      (mulVecLinR (R := R) (Matrix.GeneralLinearGroup.map (algebraMap R K) M) w) i =
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 0) * w 0 +
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) i 1) * w 1 := by
    intro i
    rw [mulVecLinR_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [map_coe_apply, map_coe_apply]
  refine ⟨fun i => ?_, algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R).det) * t,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ht, ?_⟩
  · rw [hcoord i]
    exact IsLocalization.isInteger_add
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 0))
      (IsLocalization.isInteger_mul ⟨_, rfl⟩ (hwint 1))
  · rw [hcoord 0, hcoord 1, mulVecPair_zero, mulVecPair_one,
      Matrix.det_fin_two, map_add, map_add, map_mul, map_mul, map_mul, map_mul, map_sub,
      map_mul, map_mul]

    linear_combination
      (algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 0) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 1) -
        algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 0 1) *
          algebraMap R K ((M : Matrix (Fin 2) (Fin 2) R) 1 0)) * hweq

omit [IsFractionRing R K] in

theorem latticeMap_map_interLattice (M : Matrix.GeneralLinearGroup (Fin 2) R)
    (ϖ c d : R) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
        (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) := by
  refine le_antisymm (latticeMap_map_interLattice_le M ϖ c d) ?_

  have hinv := latticeMap_map_interLattice_le (K := K) M⁻¹ ϖ
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
    (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)

  have hcomp : ∀ i : Fin 2, mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) i = ![c, d] i := by
    intro i
    rw [← mulVecPair_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    show ((1 : Matrix (Fin 2) (Fin 2) R) *ᵥ ![c, d]) i = ![c, d] i
    rw [Matrix.one_mulVec]
  rw [show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 0 = c from hcomp 0,
    show mulVecPair ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 2) R) :
        Matrix (Fin 2) (Fin 2) R)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0)
      (mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1) 1 = d from hcomp 1] at hinv

  have hmono := latticeMap_mono (R := R)
    (Matrix.GeneralLinearGroup.map (algebraMap R K) M) hinv
  rwa [← latticeMap_mul, ← map_mul, mul_inv_cancel, map_one, latticeMap_one] at hmono

end Engine

section Dichotomy

variable [IsFractionRing R K]

omit [IsFractionRing R K] in

theorem interLattice_congr {ϖ c d c' d' : R} (hc : ϖ ∣ c - c') (hd : ϖ ∣ d - d') :
    interLattice R K ϖ c d = interLattice R K ϖ c' d' := by
  have key : ∀ {a b a' b' : R}, ϖ ∣ a - a' → ϖ ∣ b - b' →
      interLattice R K ϖ a b ≤ interLattice R K ϖ a' b' := by
    rintro a b a' b' ⟨x, hx⟩ ⟨y, hy⟩ v ⟨hv, w, hw, hweq⟩
    obtain ⟨r0, hr0⟩ := hv 0
    obtain ⟨r1, hr1⟩ := hv 1
    refine ⟨hv, w - algebraMap R K y * algebraMap R K r0 +
        algebraMap R K x * algebraMap R K r1,
      IsLocalization.isInteger_add
        (isInteger_sub hw (IsLocalization.isInteger_mul ⟨y, rfl⟩ ⟨r0, rfl⟩))
        (IsLocalization.isInteger_mul ⟨x, rfl⟩ ⟨r1, rfl⟩), ?_⟩
    have ha' : algebraMap R K a' =
        algebraMap R K a - algebraMap R K ϖ * algebraMap R K x := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hx)
    have hb' : algebraMap R K b' =
        algebraMap R K b - algebraMap R K ϖ * algebraMap R K y := by
      rw [← map_mul, ← map_sub]
      exact congrArg _ (by linear_combination -hy)
    rw [ha', hb']
    linear_combination hweq + algebraMap R K ϖ * algebraMap R K y * hr0 -
      algebraMap R K ϖ * algebraMap R K x * hr1
  exact le_antisymm (key hc hd) (key (dvd_sub_comm.mp hc) (dvd_sub_comm.mp hd))

omit [IsFractionRing R K] in

theorem interLattice_unit_mul (ϖ : R) (u : Rˣ) (c d : R) :
    interLattice R K ϖ ((u : R) * c) ((u : R) * d) = interLattice R K ϖ c d := by
  have hu : algebraMap R K ((u⁻¹ : Rˣ) : R) * algebraMap R K (u : R) = 1 := by
    rw [← map_mul, ← map_one (algebraMap R K)]
    exact congrArg _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
  ext v
  rw [mem_interLattice, mem_interLattice]
  constructor
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K ((u⁻¹ : Rˣ) : R) * w,
      IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul] at hweq
    calc algebraMap R K d * v 0 - algebraMap R K c * v 1
        = algebraMap R K ((u⁻¹ : Rˣ) : R) *
            (algebraMap R K (u : R) * algebraMap R K d * v 0 -
              algebraMap R K (u : R) * algebraMap R K c * v 1) := by
          rw [mul_sub, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, hu, one_mul,
            one_mul]
      _ = algebraMap R K ϖ * (algebraMap R K ((u⁻¹ : Rˣ) : R) * w) := by
          rw [hweq]; ring
  · rintro ⟨hv, w, hw, hweq⟩
    refine ⟨hv, algebraMap R K (u : R) * w, IsLocalization.isInteger_mul ⟨_, rfl⟩ hw, ?_⟩
    rw [map_mul, map_mul]
    calc algebraMap R K (u : R) * algebraMap R K d * v 0 -
          algebraMap R K (u : R) * algebraMap R K c * v 1
        = algebraMap R K (u : R) * (algebraMap R K d * v 0 - algebraMap R K c * v 1) := by
          ring
      _ = algebraMap R K ϖ * (algebraMap R K (u : R) * w) := by rw [hweq]; ring

omit [IsFractionRing R K] in

theorem latticeMap_map_interLattice_eq_self (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (lam : Rˣ)
    (h0 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 - (lam : R) * c)
    (h1 : ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 - (lam : R) * d) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) =
      interLattice R K ϖ c d := by
  rw [latticeMap_map_interLattice, interLattice_congr h0 h1, interLattice_unit_mul]

theorem dvd_of_latticeMap_map_interLattice_eq_self
    (M : Matrix.GeneralLinearGroup (Fin 2) R) {ϖ c d : R}
    (h : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  rw [latticeMap_map_interLattice] at h
  exact dvd_of_interLattice_eq h

end Dichotomy

section Rigidity

variable [IsFractionRing R K]

omit [Algebra R K] [IsFractionRing R K] in

theorem isUnit_or_isUnit_or_associated_of_mul_eq_sq [IsDomain R] {ϖ a b : R}
    (hϖ : Prime ϖ) (h : a * b = ϖ * ϖ) :
    IsUnit a ∨ IsUnit b ∨ ∃ u : R, IsUnit u ∧ a = ϖ * u := by
  have hne : ϖ ≠ 0 := hϖ.ne_zero
  rcases hϖ.2.2 a b ⟨ϖ, by rw [← h]⟩ with ha | hb
  ·
    obtain ⟨a', rfl⟩ := ha
    have hcancel : a' * b = ϖ := by
      have h2 : ϖ * (a' * b) = ϖ * ϖ := by linear_combination h
      exact mul_left_cancel₀ hne h2
    rcases hϖ.2.2 a' b ⟨1, by rw [mul_one]; exact hcancel⟩ with ha' | hb'
    ·
      obtain ⟨a'', rfl⟩ := ha'
      have h3 : a'' * b = 1 := by
        have h2 : ϖ * (a'' * b) = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inl (IsUnit.of_mul_eq_one_right a'' h3))
    ·
      obtain ⟨b', rfl⟩ := hb'
      have h3 : a' * b' = 1 := by
        have h2 : ϖ * (a' * b') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inr ⟨a', IsUnit.of_mul_eq_one b' h3, rfl⟩)
  ·
    obtain ⟨b', rfl⟩ := hb
    have hcancel : a * b' = ϖ := by
      have h2 : ϖ * (a * b') = ϖ * ϖ := by linear_combination h
      exact mul_left_cancel₀ hne h2
    rcases hϖ.2.2 a b' ⟨1, by rw [mul_one]; exact hcancel⟩ with ha' | hb''
    ·
      obtain ⟨a', rfl⟩ := ha'
      have h3 : a' * b' = 1 := by
        have h2 : ϖ * (a' * b') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inr (Or.inr ⟨a', IsUnit.of_mul_eq_one b' h3, rfl⟩)
    ·
      obtain ⟨b'', rfl⟩ := hb''
      have h3 : a * b'' = 1 := by
        have h2 : ϖ * (a * b'') = ϖ * 1 := by rw [mul_one]; linear_combination hcancel
        exact mul_left_cancel₀ hne h2
      exact Or.inl (IsUnit.of_mul_eq_one b'' h3)

omit [IsFractionRing R K] in

theorem latticeMap_scalarGL_eq_self_of_isUnit {e : Kˣ} {u : R} (hu : IsUnit u)
    (heu : (e : K) = algebraMap R K u) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL e) L = L := by
  obtain ⟨v, rfl⟩ := hu
  ext x
  rw [mem_latticeMap_scalarGL]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [heu, algebraMap_smul]
    exact L.smul_mem _ hw
  · intro hx
    refine ⟨((v⁻¹ : Rˣ) : R) • x, L.smul_mem _ hx, ?_⟩
    rw [heu, algebraMap_smul, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_smul]

theorem isInteger_mul_algebraMap_of_latticeMap_le {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : latticeMap (scalarGL e) N ≤ stdLattice R K) :
    IsLocalization.IsInteger R ((e : K) * algebraMap R K ϖ) := by
  have h1 : (algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K) ∈
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨Pi.single 0 1, single_one_mem_stdLattice R K 0, by rw [unitOfNeZero_coe]⟩
  have h2 : (e : K) • ((algebraMap R K ϖ) • (Pi.single 0 1 : Fin 2 → K)) ∈
      latticeMap (scalarGL e) N := by
    rw [mem_latticeMap_scalarGL]
    exact ⟨_, hlow h1, rfl⟩
  have h3 := hup h2 0
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
  exact h3

theorem latticeMap_scalarGL_inv_le_of_mul_eq_unit {e : Kˣ} {ϖ : R} (hϖ : ϖ ≠ 0) {u : R}
    (hu : IsUnit u) (heu : (e : K) * algebraMap R K ϖ = algebraMap R K u)
    {N : Submodule R (Fin 2 → K)} (hN : N ≤ stdLattice R K) :
    latticeMap (scalarGL e⁻¹) N ≤
      latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) := by
  obtain ⟨v, rfl⟩ := hu

  have hprod : (e : K) *
      (algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R)) = 1 := by
    rw [← mul_assoc, heu, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      map_one]
  have hinv : ((e⁻¹ : Kˣ) : K) =
      algebraMap R K ϖ * algebraMap R K ((v⁻¹ : Rˣ) : R) := by
    have h1 := congrArg (fun z => ((e⁻¹ : Kˣ) : K) * z) hprod
    simp only [mul_one] at h1
    rw [← mul_assoc, Units.inv_mul, one_mul] at h1
    exact h1.symm
  intro x hx
  rw [mem_latticeMap_scalarGL] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  rw [mem_latticeMap_scalarGL_stdLattice hϖ]
  intro i
  obtain ⟨wi, hwi⟩ := hN hw i
  refine ⟨algebraMap R K ((v⁻¹ : Rˣ) : R) * algebraMap R K wi,
    IsLocalization.isInteger_mul ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, hinv, ← hwi]
  ring

theorem eq_of_homothetic_of_mem_interval [IsDomain R] {ϖ : R} (hϖ : Prime ϖ)
    {N N' : Submodule R (Fin 2 → K)}
    (hNlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N)
    (hNup : N ≤ stdLattice R K)
    (hN'low : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ.ne_zero)) (stdLattice R K) < N')
    (hN'up : N' ≤ stdLattice R K)
    (h : Homothetic N N') : N = N' := by
  obtain ⟨e, he⟩ := h
  have hNinv : latticeMap (scalarGL e⁻¹) N' = N := by
    rw [← he, ← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one,
      latticeMap_one]

  obtain ⟨a, ha⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hNlow.le
    (he ▸ hN'up)
  obtain ⟨b, hb⟩ := isInteger_mul_algebraMap_of_latticeMap_le hϖ.ne_zero hN'low.le
    (hNinv ▸ hNup)
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h0 =>
    hϖ.ne_zero (IsFractionRing.injective R K (h0.trans (map_zero _).symm))

  have hab : a * b = ϖ * ϖ := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ha, hb]
    calc (e : K) * algebraMap R K ϖ * (((e⁻¹ : Kˣ) : K) * algebraMap R K ϖ)
        = ((e : K) * ((e⁻¹ : Kˣ) : K)) * (algebraMap R K ϖ * algebraMap R K ϖ) := by
          ring
      _ = algebraMap R K ϖ * algebraMap R K ϖ := by rw [Units.mul_inv, one_mul]
  rcases isUnit_or_isUnit_or_associated_of_mul_eq_sq hϖ hab with hua | hub | ⟨u, hu, hau⟩
  ·
    exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e) hϖ.ne_zero hua
      ha.symm hN'up
    rw [hNinv] at hkey
    exact absurd (le_antisymm hkey hNlow.le) hNlow.ne'
  ·
    exfalso
    have hkey := latticeMap_scalarGL_inv_le_of_mul_eq_unit (e := e⁻¹) hϖ.ne_zero hub
      hb.symm hNup
    rw [inv_inv, he] at hkey
    exact absurd (le_antisymm hkey hN'low.le) hN'low.ne'
  ·
    have heu : (e : K) = algebraMap R K u := by
      have h2 : (e : K) * algebraMap R K ϖ = algebraMap R K u * algebraMap R K ϖ := by
        rw [← ha, hau, map_mul]; ring
      exact mul_right_cancel₀ hϖK h2
    rw [← he, latticeMap_scalarGL_eq_self_of_isUnit hu heu]

theorem dvd_of_isFixedVertex_interLattice [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    (hcd' : ¬(ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1))
    {hL : IsFullLattice (interLattice R K ϖ c d)}
    (h : IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL)) :
    ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1 := by
  rw [isFixedVertex_mk_iff, latticeMap_map_interLattice] at h
  have heq := eq_of_homothetic_of_mem_interval hϖ
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd')
    (interLattice_le_stdLattice _ _ _)
    (latticeMap_scalarGL_lt_interLattice hϖ.ne_zero hcd)
    (interLattice_le_stdLattice _ _ _) h
  exact dvd_of_interLattice_eq heq

theorem not_isFixedVertex_interLattice_of_not_dvd [IsDomain R]
    (M : Matrix.GeneralLinearGroup (Fin 2) R)
    {ϖ c d : R} (hϖ : Prime ϖ) (hcd : ¬(ϖ ∣ c ∧ ϖ ∣ d))
    (hcd' : ¬(ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 ∧
      ϖ ∣ mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1))
    (hnofix : ¬ ϖ ∣ d * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 0 -
      c * mulVecPair (M : Matrix (Fin 2) (Fin 2) R) c d 1)
    {hL : IsFullLattice (interLattice R K ϖ c d)} :
    ¬ IsFixedVertex (Matrix.GeneralLinearGroup.map (algebraMap R K) M)
      (Vertex.mk R K (interLattice R K ϖ c d) hL) :=
  fun h => hnofix (dvd_of_isFixedVertex_interLattice M hϖ hcd hcd' h)

end Rigidity

section FullLattice

variable [IsFractionRing R K]

theorem isFullLattice_of_le_of_le [IsNoetherianRing R] {ϖ : R} (hϖ : ϖ ≠ 0)
    {N : Submodule R (Fin 2 → K)}
    (hlow : latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K) ≤ N)
    (hup : N ≤ stdLattice R K) : IsFullLattice N := by
  constructor
  ·
    haveI : IsNoetherian R (stdLattice R K) :=
      isNoetherian_of_fg_of_noetherian _ (stdLattice_fg R K)
    have h1 : (Submodule.comap (stdLattice R K).subtype N).FG :=
      IsNoetherian.noetherian _
    have h2 := Submodule.FG.map (f := (stdLattice R K).subtype) h1
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hup] at h2
  ·
    have hfull : IsFullLattice
        (latticeMap (scalarGL (unitOfNeZero (K := K) hϖ)) (stdLattice R K)) :=
      (isFullLattice_stdLattice).map _
    rw [eq_top_iff, ← hfull.2]
    exact Submodule.span_mono hlow

theorem isFullLattice_interLattice [IsNoetherianRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    (c d : R) : IsFullLattice (interLattice R K ϖ c d) :=
  isFullLattice_of_le_of_le hϖ.ne_zero
    (latticeMap_scalarGL_le_interLattice hϖ.ne_zero c d)
    (interLattice_le_stdLattice ϖ c d)

end FullLattice

section PadicGates

noncomputable def gammaZero : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

@[simp] theorem gammaZero_coe :
    (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![0, -1; 1, -1] :=
  IsUnit.unit_spec _

noncomputable def transvectionGate : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2] :=
  ((Matrix.isUnit_iff_isUnit_det
      (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ_[2])).mpr
    (by rw [Matrix.det_fin_two_of]; norm_num)).unit

@[simp] theorem transvectionGate_coe :
    (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) = !![1, 1; 0, 1] :=
  IsUnit.unit_spec _

theorem not_two_dvd_one_padic : ¬ ((2 : ℤ_[2]) ∣ 1) := fun h =>
  (PadicInt.irreducible_p (p := 2)).not_isUnit (isUnit_of_dvd_one h)

example : IsFixedVertex
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
    (stdVertex ℤ_[2] ℚ_[2]) :=
  isFixedVertex_stdVertex_of_mem_range ⟨gammaZero, rfl⟩

example : ¬ IsFixedVertex
    (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
    (Vertex.mk ℤ_[2] ℚ_[2] (interLattice ℤ_[2] ℚ_[2] 2 1 0)
      (isFullLattice_interLattice PadicInt.irreducible_p 1 0)) := by
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 0 = 0 := by
    simp
  have hv1 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 1 = 1 := by
    simp
  refine not_isFixedVertex_interLattice_of_not_dvd gammaZero PadicInt.prime_p
    (fun h => not_two_dvd_one_padic h.1) ?_ ?_
  · rw [hv0, hv1]
    exact fun h => not_two_dvd_one_padic h.2
  · rw [hv0, hv1]
    intro hcon
    apply not_two_dvd_one_padic
    apply dvd_neg.mp
    have hval : (0 : ℤ_[2]) * 0 - 1 * 1 = -1 := by ring
    rwa [hval] at hcon

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (interLattice ℤ_[2] ℚ_[2] 2 0 1) ≠ interLattice ℤ_[2] ℚ_[2] 2 0 1 := by
  intro h
  have hd := dvd_of_latticeMap_map_interLattice_eq_self gammaZero h
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 0 = -1 := by
    simp
  have hval : (1 : ℤ_[2]) * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 0 -
      0 * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 0 1 1 = -1 := by
    rw [hv0]; ring
  rw [hval] at hd
  exact not_two_dvd_one_padic (dvd_neg.mp hd)

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (interLattice ℤ_[2] ℚ_[2] 2 1 1) ≠ interLattice ℤ_[2] ℚ_[2] 2 1 1 := by
  intro h
  have hd := dvd_of_latticeMap_map_interLattice_eq_self gammaZero h
  have hv0 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 0 = -1 := by
    simp
  have hv1 : mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 1 = 0 := by
    simp
  have hval : (1 : ℤ_[2]) * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 0 -
      1 * mulVecPair (gammaZero : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 1 1 = -1 := by
    rw [hv0, hv1]; ring
  rw [hval] at hd
  exact not_two_dvd_one_padic (dvd_neg.mp hd)

example :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) transvectionGate)
        (interLattice ℤ_[2] ℚ_[2] 2 1 0) = interLattice ℤ_[2] ℚ_[2] 2 1 0 := by
  refine latticeMap_map_interLattice_eq_self transvectionGate 1 ?_ ?_
  · have hv : mulVecPair (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 0 = 1 := by
      simp
    rw [hv]
    simp
  · have hv : mulVecPair (transvectionGate : Matrix (Fin 2) (Fin 2) ℤ_[2]) 1 0 1 = 0 := by
      simp
    rw [hv]
    simp

example : ¬ (fixedVertexSet (R := ℤ_[2])
    (scalarGL (Units.mk0 (2 : ℚ_[2]) (by norm_num)))).Subsingleton :=
  not_subsingleton_fixedVertexSet_scalarGL PadicInt.irreducible_p _

end PadicGates

end LT.LatticeTree

set_option autoImplicit false

open scoped Matrix

namespace LT.LatticeTree

attribute [local simp] mem_stdLattice latticeMap_one IntegralAut.symm_toField IntegralAut.symm_toBase galVec_symm_galVec galVec_galVec_symm latticeGal_symm_latticeGal latticeGal_latticeGal_symm mem_fixedVertexSet

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

def Vertex.twistedAct (δ : Matrix.GeneralLinearGroup (Fin 2) K) (σ : IntegralAut R K)
    (v : Vertex R K) : Vertex R K :=
  Vertex.act δ (Vertex.galAct σ v)

theorem Vertex.twistedAct_mk (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (L : Submodule R (Fin 2 → K)) (hL : IsFullLattice L) :
    Vertex.twistedAct δ σ (Vertex.mk R K L hL) =
      Vertex.mk R K (twistedLatticeMap δ σ L) ((hL.gal σ).map δ) :=
  rfl

theorem Vertex.galAct_refl (v : Vertex R K) :
    Vertex.galAct (IntegralAut.refl R K) v = v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.galAct (IntegralAut.refl R K) (Vertex.mk R K L.1 L.2) =
      Vertex.mk R K L.1 L.2
    rw [Vertex.galAct_mk, Vertex.mk_eq_mk_iff, latticeGal_refl]
    exact Homothetic.refl _

theorem Vertex.twistedAct_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (v : Vertex R K) :
    Vertex.twistedAct δ (IntegralAut.refl R K) v = Vertex.act δ v := by
  rw [Vertex.twistedAct, Vertex.galAct_refl]

def IsTwistedFixedVertex (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) (v : Vertex R K) : Prop :=
  Vertex.twistedAct δ σ v = v

def twistedFixedVertexSet (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : Set (Vertex R K) :=
  {v | IsTwistedFixedVertex δ σ v}

theorem mem_twistedFixedVertexSet {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    {σ : IntegralAut R K} {v : Vertex R K} :
    v ∈ twistedFixedVertexSet δ σ ↔ Vertex.twistedAct δ σ v = v :=
  Iff.rfl

attribute [local simp] mem_twistedFixedVertexSet
noncomputable def twistedUnitOrbitalCount (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (σ : IntegralAut R K) : ℕ :=
  Nat.card (twistedFixedVertexSet δ σ)

theorem twistedFixedVertexSet_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedFixedVertexSet δ (IntegralAut.refl R K) = fixedVertexSet (R := R) δ := by
  ext v
  rw [mem_twistedFixedVertexSet, mem_fixedVertexSet, Vertex.twistedAct_refl]

theorem twistedUnitOrbitalCount_refl (δ : Matrix.GeneralLinearGroup (Fin 2) K) :
    twistedUnitOrbitalCount δ (IntegralAut.refl R K) = unitOrbitalCount R δ := by
  rw [twistedUnitOrbitalCount, unitOrbitalCount, twistedFixedVertexSet_refl]

theorem Vertex.twistedAct_three_of_orderThree (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (v : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.twistedAct δ σ v)) =
      Vertex.act (normThree δ σ) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.twistedAct δ σ
      (Vertex.mk R K L.1 L.2))) = Vertex.act (normThree δ σ) (Vertex.mk R K L.1 L.2)
    rw [Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.act_mk,
      Vertex.mk_eq_mk_iff, twistedLatticeMap_three_of_orderThree δ hσ]
    exact Homothetic.refl _

theorem Vertex.twistedAct_two_of_orderTwo (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    {σ : IntegralAut R K} (hσ : σ.comp σ = IntegralAut.refl R K) (v : Vertex R K) :
    Vertex.twistedAct δ σ (Vertex.twistedAct δ σ v) = Vertex.act (normTwo δ σ) v := by
  induction v using Quotient.inductionOn with
  | h L =>
    show Vertex.twistedAct δ σ (Vertex.twistedAct δ σ (Vertex.mk R K L.1 L.2)) =
      Vertex.act (normTwo δ σ) (Vertex.mk R K L.1 L.2)
    rw [Vertex.twistedAct_mk, Vertex.twistedAct_mk, Vertex.act_mk, Vertex.mk_eq_mk_iff,
      twistedLatticeMap_two_of_orderTwo δ hσ]
    exact Homothetic.refl _

theorem isFixedVertex_normThree_of_isTwistedFixedVertex
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K) {v : Vertex R K}
    (hv : IsTwistedFixedVertex δ σ v) : IsFixedVertex (normThree δ σ) v := by
  have hv' : Vertex.twistedAct δ σ v = v := hv
  show Vertex.act (normThree δ σ) v = v
  rw [← Vertex.twistedAct_three_of_orderThree δ hσ, hv', hv', hv']

theorem isFixedVertex_normTwo_of_isTwistedFixedVertex
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) {v : Vertex R K}
    (hv : IsTwistedFixedVertex δ σ v) : IsFixedVertex (normTwo δ σ) v := by
  have hv' : Vertex.twistedAct δ σ v = v := hv
  show Vertex.act (normTwo δ σ) v = v
  rw [← Vertex.twistedAct_two_of_orderTwo δ hσ, hv', hv']

theorem twistedFixedVertexSet_subset_fixedVertexSet_normThree
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K) :
    twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) (normThree δ σ) :=
  fun _ hv => isFixedVertex_normThree_of_isTwistedFixedVertex δ hσ hv

theorem twistedFixedVertexSet_subset_fixedVertexSet_normTwo
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) :
    twistedFixedVertexSet δ σ ⊆ fixedVertexSet (R := R) (normTwo δ σ) :=
  fun _ hv => isFixedVertex_normTwo_of_isTwistedFixedVertex δ hσ hv

theorem isTwistedFixedVertex_stdVertex_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    IsTwistedFixedVertex δ σ (stdVertex R K) := by
  show Vertex.twistedAct δ σ (stdVertex R K) = stdVertex R K
  rw [Vertex.twistedAct, Vertex.galAct_stdVertex]
  exact isFixedVertex_stdVertex_of_mem_range hδ

theorem nonempty_twistedFixedVertexSet_of_mem_range [IsFractionRing R K]
    {δ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hδ : δ ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (σ : IntegralAut R K) :
    (twistedFixedVertexSet δ σ).Nonempty :=
  ⟨stdVertex R K, isTwistedFixedVertex_stdVertex_of_mem_range hδ σ⟩

theorem twistedFixedVertexSet_eq_singleton_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedFixedVertexSet δ σ = {v₀} :=
  Set.eq_singleton_iff_unique_mem.mpr
    ⟨hv₀, fun _ hw => hsub (hincl hw) (hincl hv₀)⟩

theorem twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    {δ : Matrix.GeneralLinearGroup (Fin 2) K} {σ : IntegralAut R K}
    {s : Set (Vertex R K)} (hincl : twistedFixedVertexSet δ σ ⊆ s)
    (hsub : s.Subsingleton) {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 := by
  rw [twistedUnitOrbitalCount,
    twistedFixedVertexSet_eq_singleton_of_subset_subsingleton hincl hsub hv₀,
    Nat.card_coe_set_eq, Set.ncard_singleton]

theorem unitOrbitalCount_eq_one_of_subsingleton
    {γ : Matrix.GeneralLinearGroup (Fin 2) K}
    (hsub : (fixedVertexSet (R := R) γ).Subsingleton) {w₀ : Vertex R K}
    (hw₀ : IsFixedVertex γ w₀) : unitOrbitalCount R γ = 1 := by
  have heq : fixedVertexSet (R := R) γ = {w₀} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hw₀, fun _ hx => hsub hx hw₀⟩
  rw [unitOrbitalCount, heq, Nat.card_coe_set_eq, Set.ncard_singleton]

theorem twistedUnitOrbitalCount_eq_one_of_subsingleton_normThree
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (hsub : (fixedVertexSet (R := R) (normThree δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 :=
  twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    (twistedFixedVertexSet_subset_fixedVertexSet_normThree δ hσ) hsub hv₀

theorem twistedUnitOrbitalCount_eq_one_of_subsingleton_normTwo
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K)
    (hsub : (fixedVertexSet (R := R) (normTwo δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀) :
    twistedUnitOrbitalCount δ σ = 1 :=
  twistedUnitOrbitalCount_eq_one_of_subset_subsingleton
    (twistedFixedVertexSet_subset_fixedVertexSet_normTwo δ hσ) hsub hv₀

section FundamentalLemma

variable {R' : Type*} [CommRing R'] {K' : Type*} [Field K'] [Algebra R' K']

theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_subsingleton
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : (σ.comp σ).comp σ = IntegralAut.refl R K)
    (hsub_up : (fixedVertexSet (R := R) (normThree δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K')
    (hsub_down : (fixedVertexSet (R := R') γ).Subsingleton)
    {w₀ : Vertex R' K'} (hw₀ : IsFixedVertex γ w₀) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount R' γ := by
  rw [twistedUnitOrbitalCount_eq_one_of_subsingleton_normThree δ hσ hsub_up hv₀,
    unitOrbitalCount_eq_one_of_subsingleton hsub_down hw₀]

theorem twistedUnitOrbitalCount_eq_unitOrbitalCount_of_subsingleton_two
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K)
    (hsub_up : (fixedVertexSet (R := R) (normTwo δ σ)).Subsingleton)
    {v₀ : Vertex R K} (hv₀ : IsTwistedFixedVertex δ σ v₀)
    (γ : Matrix.GeneralLinearGroup (Fin 2) K')
    (hsub_down : (fixedVertexSet (R := R') γ).Subsingleton)
    {w₀ : Vertex R' K'} (hw₀ : IsFixedVertex γ w₀) :
    twistedUnitOrbitalCount δ σ = unitOrbitalCount R' γ := by
  rw [twistedUnitOrbitalCount_eq_one_of_subsingleton_normTwo δ hσ hsub_up hv₀,
    unitOrbitalCount_eq_one_of_subsingleton hsub_down hw₀]

end FundamentalLemma

theorem latticeGal_interLattice_le (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) ≤
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwint, t, ht, hweq⟩ := hw
  refine ⟨fun i => σ.isInteger_map (hwint i), σ.toField t, σ.isInteger_map ht, ?_⟩
  have key : algebraMap R K (σ.toBase d) * σ.toField (w 0) -
      algebraMap R K (σ.toBase c) * σ.toField (w 1) =
        algebraMap R K (σ.toBase ϖ) * σ.toField t := by
    rw [← σ.commutes d, ← σ.commutes c, ← σ.commutes ϖ]
    calc σ.toField (algebraMap R K d) * σ.toField (w 0) -
          σ.toField (algebraMap R K c) * σ.toField (w 1)
        = σ.toField (algebraMap R K d * w 0 - algebraMap R K c * w 1) := by
          rw [map_sub, map_mul, map_mul]
      _ = σ.toField (algebraMap R K ϖ * t) := by rw [hweq]
      _ = σ.toField (algebraMap R K ϖ) * σ.toField t := by rw [map_mul]
  rw [galVec_apply, galVec_apply]
  exact key

theorem latticeGal_interLattice (σ : IntegralAut R K) (ϖ c d : R) :
    latticeGal σ (interLattice R K ϖ c d) =
      interLattice R K (σ.toBase ϖ) (σ.toBase c) (σ.toBase d) := by
  refine le_antisymm (latticeGal_interLattice_le σ ϖ c d) ?_
  have h := latticeGal_interLattice_le σ.symm (σ.toBase ϖ) (σ.toBase c) (σ.toBase d)
  rw [IntegralAut.symm_toBase, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply] at h
  intro v hv
  exact ⟨galVec σ.symm v, h (galVec_mem_latticeGal hv), galVec_galVec_symm σ v⟩

theorem twistedLatticeMap_map_interLattice (δ : Matrix.GeneralLinearGroup (Fin 2) R)
    (σ : IntegralAut R K) {ϖ : R} (hϖ : σ.toBase ϖ = ϖ) (c d : R) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) =
      interLattice R K ϖ
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0)
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1) := by
  rw [twistedLatticeMap, latticeGal_interLattice, hϖ, latticeMap_map_interLattice]

theorem dvd_of_twistedLatticeMap_map_interLattice_eq_self [IsFractionRing R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) R) (σ : IntegralAut R K) {ϖ : R}
    (hϖ : σ.toBase ϖ = ϖ) {c d : R}
    (h : twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap R K) δ) σ
        (interLattice R K ϖ c d) = interLattice R K ϖ c d) :
    ϖ ∣ d * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 0 -
        c * mulVecPair (δ : Matrix (Fin 2) (Fin 2) R) (σ.toBase c) (σ.toBase d) 1 := by
  rw [twistedLatticeMap_map_interLattice δ σ hϖ c d] at h
  exact dvd_of_interLattice_eq h

example :
    twistedUnitOrbitalCount
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
        (IntegralAut.refl ℤ_[2] ℚ_[2]) =
      unitOrbitalCount ℤ_[2]
        (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero) :=
  twistedUnitOrbitalCount_refl _

example :
    IsTwistedFixedVertex
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) gammaZero)
      (IntegralAut.refl ℤ_[2] ℚ_[2]) (stdVertex ℤ_[2] ℚ_[2]) :=
  isTwistedFixedVertex_stdVertex_of_mem_range ⟨gammaZero, rfl⟩ _

example : ¬ (twistedFixedVertexSet (R := ℤ_[2])
    (scalarGL (Units.mk0 (2 : ℚ_[2]) (by norm_num)))
    (IntegralAut.refl ℤ_[2] ℚ_[2])).Subsingleton := by
  rw [twistedFixedVertexSet_refl]
  exact not_subsingleton_fixedVertexSet_scalarGL PadicInt.irreducible_p _

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℤ_[2]) (c d : ℤ_[2]) :
    twistedLatticeMap (Matrix.GeneralLinearGroup.map (algebraMap ℤ_[2] ℚ_[2]) δ)
        (IntegralAut.refl ℤ_[2] ℚ_[2]) (interLattice ℤ_[2] ℚ_[2] 2 c d) =
      interLattice ℤ_[2] ℚ_[2] 2
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) ℤ_[2]) c d 0)
        (mulVecPair (δ : Matrix (Fin 2) (Fin 2) ℤ_[2]) c d 1) :=
  twistedLatticeMap_map_interLattice δ (IntegralAut.refl ℤ_[2] ℚ_[2]) rfl c d

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℂ) (v : Vertex ℂ ℂ)
    (hv : IsTwistedFixedVertex δ conjAut v) : IsFixedVertex (normTwo δ conjAut) v :=
  isFixedVertex_normTwo_of_isTwistedFixedVertex δ conjAut_comp_conjAut hv

example :
    latticeGal conjAut (interLattice ℂ ℂ 0 1 Complex.I) =
      interLattice ℂ ℂ (conjAut.toBase 0) (conjAut.toBase 1)
        (conjAut.toBase Complex.I) :=
  latticeGal_interLattice conjAut 0 1 Complex.I

example :
    latticeGal conjAut (interLattice ℂ ℂ 0 1 Complex.I) ≠
      interLattice ℂ ℂ 0 1 Complex.I := by
  rw [latticeGal_interLattice,
    show conjAut.toBase (0 : ℂ) = 0 from map_zero _,
    show conjAut.toBase (1 : ℂ) = 1 from map_one _,
    show conjAut.toBase Complex.I = -Complex.I from Complex.conj_I]
  intro h
  have hd := dvd_of_interLattice_eq h

  rw [zero_dvd_iff] at hd
  apply complex_I_ne_neg_I
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination hd
  have hI : Complex.I = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' (by norm_num)
    · exact h'
  rw [hI, neg_zero]

end LT.LatticeTree


