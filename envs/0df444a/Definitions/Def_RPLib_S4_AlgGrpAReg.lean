-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpAReg
-- name    : RPLib_S4_AlgGrpAReg
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T02:34:45.149465+00:00
-- url     : https://prove2.me/theorems/63482ab8-9d80-4315-8e34-f7fa9f7b1262
-- title:
--   Larsen's alternative library: regular functions on `GL_n(K)` and
-- statement:
--   Regular functions are the polynomials in the coordinates `crd` (entries of `g` and `g⁻¹`); they form
--   the subalgebra `regFun`. Regular matrix-valued maps (`IsRegMat`) are closed under products,
--   Kronecker products and transposes, and contain `g` and `g⁻¹`; this covers every tensor construction
--   `V^{⊗a} ⊗ (V^∨)^{⊗b}`.: a polynomial identity that holds on a set `H` holds on its Zariski closure; hence a regular
--   representation has the same invariant vectors and the same commutant on `H` and on its closure.
--   Regular maps are continuous, so kernels of regular homomorphisms are closed.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpAZar

/-!
# S4-AlgGrpA, file Reg: regular functions on `GL_n(K)` and (A1)

Regular functions are the polynomials in the coordinates `crd` (entries of `g` and `g⁻¹`); they form
the subalgebra `regFun`. Regular matrix-valued maps (`IsRegMat`) are closed under products,
Kronecker products and transposes, and contain `g` and `g⁻¹`; this covers every tensor construction
`V^{⊗a} ⊗ (V^∨)^{⊗b}`.

(A1): a polynomial identity that holds on a set `H` holds on its Zariski closure; hence a regular
representation has the same invariant vectors and the same commutant on `H` and on its closure.
Regular maps are continuous, so kernels of regular homomorphisms are closed.
-/

set_option autoImplicit false

open MvPolynomial

noncomputable section

namespace RamanujanPetersson.AlgGrpA

attribute [local instance] zarTop

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- Polynomials in the coordinates, as functions on `GL_n(K)`. -/
def polyFun : MvPolynomial (Var n) K →ₐ[K] (Matrix.GeneralLinearGroup n K → K) :=
  AlgHom.pi (fun g => aeval (crd g))

theorem polyFun_apply (p : MvPolynomial (Var n) K) (g : Matrix.GeneralLinearGroup n K) :
    polyFun p g = eval (crd g) p := rfl

/-- The algebra of regular functions on `GL_n(K)`. -/
def regFun : Subalgebra K (Matrix.GeneralLinearGroup n K → K) := (polyFun (n := n) (K := K)).range

/-- `f` is a regular function: a polynomial in the entries of `g` and of `g⁻¹`. -/
def IsRegFun (f : Matrix.GeneralLinearGroup n K → K) : Prop := f ∈ regFun

theorem isRegFun_iff {f : Matrix.GeneralLinearGroup n K → K} :
    IsRegFun f ↔ ∃ p : MvPolynomial (Var n) K, ∀ g, f g = eval (crd g) p := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).1 h
    exact ⟨p, fun g => by rw [← hp]; rfl⟩
  · rintro ⟨p, hp⟩
    exact (AlgHom.mem_range _).2 ⟨p, funext fun g => by rw [polyFun_apply]; exact (hp g).symm⟩

namespace IsRegFun

variable {f f₁ f₂ : Matrix.GeneralLinearGroup n K → K}

theorem const (c : K) : IsRegFun (fun _ : Matrix.GeneralLinearGroup n K => c) :=
  isRegFun_iff.2 ⟨C c, fun g => by simp⟩

theorem entry (i j : n) : IsRegFun (fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K) i j) :=
  isRegFun_iff.2 ⟨X (Sum.inl (i, j)), fun g => by simp⟩

theorem invEntry (i j : n) : IsRegFun (fun g : Matrix.GeneralLinearGroup n K =>
    ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) i j) :=
  isRegFun_iff.2 ⟨X (Sum.inr (i, j)), fun g => by simp⟩

theorem add (h₁ : IsRegFun f₁) (h₂ : IsRegFun f₂) : IsRegFun (fun g => f₁ g + f₂ g) :=
  Subalgebra.add_mem _ h₁ h₂

theorem mul (h₁ : IsRegFun f₁) (h₂ : IsRegFun f₂) : IsRegFun (fun g => f₁ g * f₂ g) :=
  Subalgebra.mul_mem _ h₁ h₂

theorem neg (h : IsRegFun f) : IsRegFun (fun g => -f g) := Subalgebra.neg_mem _ h

theorem sub (h₁ : IsRegFun f₁) (h₂ : IsRegFun f₂) : IsRegFun (fun g => f₁ g - f₂ g) :=
  Subalgebra.sub_mem _ h₁ h₂

theorem pow (h : IsRegFun f) (k : ℕ) : IsRegFun (fun g => f g ^ k) := Subalgebra.pow_mem _ h k

theorem sum {ι : Type*} (s : Finset ι) {F : ι → Matrix.GeneralLinearGroup n K → K}
    (h : ∀ i ∈ s, IsRegFun (F i)) : IsRegFun (fun g => ∑ i ∈ s, F i g) := by
  have e : (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, F i := by
    funext g
    simp [Finset.sum_apply]
  unfold IsRegFun
  rw [e]
  exact sum_mem h

theorem prod {ι : Type*} (s : Finset ι) {F : ι → Matrix.GeneralLinearGroup n K → K}
    (h : ∀ i ∈ s, IsRegFun (F i)) : IsRegFun (fun g => ∏ i ∈ s, F i g) := by
  have e : (fun g => ∏ i ∈ s, F i g) = ∏ i ∈ s, F i := by
    funext g
    simp [Finset.prod_apply]
  unfold IsRegFun
  rw [e]
  exact prod_mem h

theorem det : IsRegFun (fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K).det) := by
  refine isRegFun_iff.2
    ⟨(Matrix.of fun i j => (X (Sum.inl (i, j)) : MvPolynomial (Var n) K)).det, fun g => ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply]

/-- The zero set of a regular function is Zariski closed. -/
theorem isClosed_zero (hf : IsRegFun f) : IsClosed {g | f g = 0} := by
  obtain ⟨p, hp⟩ := isRegFun_iff.1 hf
  have : {g | f g = 0} = zeroS {p} := by
    ext g
    simp [mem_zeroS, hp]
  rw [this]
  exact isClosed_zeroS _

theorem isClosed_eq (h₁ : IsRegFun f₁) (h₂ : IsRegFun f₂) : IsClosed {g | f₁ g = f₂ g} := by
  have := (h₁.sub h₂).isClosed_zero
  simpa [sub_eq_zero] using this

end IsRegFun

/-- `ρ` is regular: every matrix entry is a regular function. -/
def IsRegMat {m m' : Type*} (ρ : Matrix.GeneralLinearGroup n K → Matrix m m' K) : Prop :=
  ∀ i j, IsRegFun (fun g => ρ g i j)

namespace IsRegMat

variable {m m' m'' : Type*}

theorem coe : IsRegMat (fun g : Matrix.GeneralLinearGroup n K => (g : Matrix n n K)) :=
  fun i j => IsRegFun.entry i j

theorem inv : IsRegMat (fun g : Matrix.GeneralLinearGroup n K =>
    ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) :=
  fun i j => IsRegFun.invEntry i j

theorem const (A : Matrix m m' K) : IsRegMat (fun _ : Matrix.GeneralLinearGroup n K => A) :=
  fun i j => IsRegFun.const (A i j)

theorem add {ρ₁ ρ₂ : Matrix.GeneralLinearGroup n K → Matrix m m' K} (h₁ : IsRegMat ρ₁)
    (h₂ : IsRegMat ρ₂) : IsRegMat (fun g => ρ₁ g + ρ₂ g) :=
  fun i j => (h₁ i j).add (h₂ i j)

theorem mul [Fintype m'] {ρ₁ : Matrix.GeneralLinearGroup n K → Matrix m m' K}
    {ρ₂ : Matrix.GeneralLinearGroup n K → Matrix m' m'' K} (h₁ : IsRegMat ρ₁) (h₂ : IsRegMat ρ₂) :
    IsRegMat (fun g => ρ₁ g * ρ₂ g) := fun i j => by
  simp only [Matrix.mul_apply]
  exact IsRegFun.sum _ fun k _ => (h₁ i k).mul (h₂ k j)

theorem transpose {ρ : Matrix.GeneralLinearGroup n K → Matrix m m' K} (h : IsRegMat ρ) :
    IsRegMat (fun g => (ρ g).transpose) := fun i j => h j i

theorem kronecker {l l' : Type*} {ρ₁ : Matrix.GeneralLinearGroup n K → Matrix m m' K}
    {ρ₂ : Matrix.GeneralLinearGroup n K → Matrix l l' K} (h₁ : IsRegMat ρ₁) (h₂ : IsRegMat ρ₂) :
    IsRegMat (fun g => Matrix.kronecker (ρ₁ g) (ρ₂ g)) := by
  rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  show IsRegFun (fun g => ρ₁ g i₁ j₁ * ρ₂ g i₂ j₂)
  exact (h₁ i₁ j₁).mul (h₂ i₂ j₂)

theorem mulVec [Fintype m'] {ρ : Matrix.GeneralLinearGroup n K → Matrix m m' K} (h : IsRegMat ρ)
    (v : m' → K) (i : m) : IsRegFun (fun g => Matrix.mulVec (ρ g) v i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact IsRegFun.sum _ fun k _ => (h i k).mul (IsRegFun.const (v k))

end IsRegMat

/-! ### (A1): identities pass to the Zariski closure -/

section A1

variable {H : Set (Matrix.GeneralLinearGroup n K)}

theorem regFun_eq_on_closure {f₁ f₂ : Matrix.GeneralLinearGroup n K → K} (h₁ : IsRegFun f₁)
    (h₂ : IsRegFun f₂) (h : ∀ g ∈ H, f₁ g = f₂ g) : ∀ g ∈ closure H, f₁ g = f₂ g :=
  fun _ hg => closure_minimal (fun x hx => h x hx) (h₁.isClosed_eq h₂) hg

theorem regMat_eq_on_closure {m m' : Type*} {ρ₁ ρ₂ : Matrix.GeneralLinearGroup n K → Matrix m m' K}
    (h₁ : IsRegMat ρ₁) (h₂ : IsRegMat ρ₂) (h : ∀ g ∈ H, ρ₁ g = ρ₂ g) :
    ∀ g ∈ closure H, ρ₁ g = ρ₂ g := fun g hg => Matrix.ext fun i j =>
  regFun_eq_on_closure (h₁ i j) (h₂ i j) (fun x hx => by rw [h x hx]) g hg

/-- (A1) Vectors fixed by a regular representation on `H` are fixed on its closure. -/
theorem fixed_on_closure {m : Type*} [Fintype m] {ρ : Matrix.GeneralLinearGroup n K → Matrix m m K}
    (hρ : IsRegMat ρ) (v : m → K) (h : ∀ g ∈ H, Matrix.mulVec (ρ g) v = v) :
    ∀ g ∈ closure H, Matrix.mulVec (ρ g) v = v := fun g hg => funext fun i =>
  regFun_eq_on_closure (hρ.mulVec v i) (IsRegFun.const (v i)) (fun x hx => by rw [h x hx]) g hg

theorem fixed_closure_iff {m : Type*} [Fintype m] {ρ : Matrix.GeneralLinearGroup n K → Matrix m m K}
    (hρ : IsRegMat ρ) (v : m → K) :
    (∀ g ∈ closure H, Matrix.mulVec (ρ g) v = v) ↔ ∀ g ∈ H, Matrix.mulVec (ρ g) v = v :=
  ⟨fun h g hg => h g (subset_closure hg), fixed_on_closure hρ v⟩

/-- (A1) The commutant of a regular representation is the same on `H` and on its closure
(for `ρ g = g ⊗ g` this is `End(V ⊗ V)^H = End(V ⊗ V)^{closure H}`, i.e. the fourth moment). -/
theorem commute_on_closure {m : Type*} [Fintype m] {ρ : Matrix.GeneralLinearGroup n K → Matrix m m K}
    (hρ : IsRegMat ρ) (A : Matrix m m K) (h : ∀ g ∈ H, ρ g * A = A * ρ g) :
    ∀ g ∈ closure H, ρ g * A = A * ρ g :=
  regMat_eq_on_closure (hρ.mul (IsRegMat.const A)) ((IsRegMat.const A).mul hρ) h

theorem commute_closure_iff {m : Type*} [Fintype m]
    {ρ : Matrix.GeneralLinearGroup n K → Matrix m m K} (hρ : IsRegMat ρ) (A : Matrix m m K) :
    (∀ g ∈ closure H, ρ g * A = A * ρ g) ↔ ∀ g ∈ H, ρ g * A = A * ρ g :=
  ⟨fun h g hg => h g (subset_closure hg), commute_on_closure hρ A⟩

/-- The tensor-square representation `g ↦ g ⊗ g` is regular. -/
theorem isRegMat_kron_self :
    IsRegMat (fun g : Matrix.GeneralLinearGroup n K =>
      Matrix.kronecker (g : Matrix n n K) (g : Matrix n n K)) :=
  IsRegMat.coe.kronecker IsRegMat.coe

end A1

/-! ### Regular maps -/

/-- A map `GL_n → GL_m` whose coordinates are regular functions. -/
def IsRegMap {m : Type*} [Fintype m] [DecidableEq m]
    (φ : Matrix.GeneralLinearGroup n K → Matrix.GeneralLinearGroup m K) : Prop :=
  ∀ v, IsRegFun (fun g => crd (φ g) v)

theorem IsRegMap.of_regMat {m : Type*} [Fintype m] [DecidableEq m]
    {φ : Matrix.GeneralLinearGroup n K → Matrix.GeneralLinearGroup m K}
    (h₁ : IsRegMat (fun g => (φ g : Matrix m m K)))
    (h₂ : IsRegMat (fun g => ((φ g)⁻¹ : Matrix.GeneralLinearGroup m K).1)) : IsRegMap φ := by
  rintro (⟨i, j⟩ | ⟨i, j⟩)
  · exact h₁ i j
  · exact h₂ i j

theorem IsRegMap.continuous {m : Type*} [Fintype m] [DecidableEq m]
    {φ : Matrix.GeneralLinearGroup n K → Matrix.GeneralLinearGroup m K} (hφ : IsRegMap φ) :
    Continuous φ := by
  choose q hq using fun v => isRegFun_iff.1 (hφ v)
  exact continuous_of_poly φ q fun g v => hq v g

/-- Kernels of regular homomorphisms are Zariski closed. -/
theorem isClosed_ker {m : Type*} [Fintype m] [DecidableEq m]
    (ρ : Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup m K)
    (hρ : IsRegMap ρ) : IsClosed (ρ.ker : Set (Matrix.GeneralLinearGroup n K)) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage hρ.continuous

/-- Regular maps send the closure of `H` into the closure of the image of `H`. -/
theorem image_closure_subset {m : Type*} [Fintype m] [DecidableEq m]
    {φ : Matrix.GeneralLinearGroup n K → Matrix.GeneralLinearGroup m K} (hφ : IsRegMap φ)
    (H : Set (Matrix.GeneralLinearGroup n K)) : φ '' closure H ⊆ closure (φ '' H) :=
  image_closure_subset_closure_image hφ.continuous

end RamanujanPetersson.AlgGrpA

end


