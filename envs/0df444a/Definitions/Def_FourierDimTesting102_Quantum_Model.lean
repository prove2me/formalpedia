-- Prove2me | Definitions.Def_FourierDimTesting102_Quantum_Model
-- name    : FourierDimTesting102_Quantum_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:09.091684+00:00
-- url     : https://prove2.me/theorems/07df3556-ee0c-42af-a117-77e3d6e85941
-- title:
--   Fourier dimension, the classes $D_k$ and $C_U$, distance, weights and the spectral projection
-- statement:
--   Write $V_n=\mathbb F_2^n$ for the set of all $n$-bit vectors, with coordinatewise addition modulo 2. A boolean function is $f:V_n\to\{-1,1\}$, recorded by the bit $b_f$ with $f(x)=(-1)^{b_f(x)}$. With the character $\chi_s(x)=(-1)^{\langle s,x\rangle}$, the Fourier coefficient is
--
--   $$
--   \widehat f(s)=2^{-n}\sum_{x\in V_n}f(x)\chi_s(x).
--   $$
--
--   The Fourier dimension of $f$ is the dimension over $\mathbb F_2$ of the span of $\{s:\widehat f(s)\neq0\}$, a set that includes $0$ when $\widehat f(0)\ne0$. The class $D_k$ consists of the boolean functions of Fourier dimension at most $k$. For a linear subspace $U\le V_n$, the class $C_U$ consists of the boolean functions $g$ with $\operatorname{supp}\widehat g\subseteq U$.
--
--   The distance is $\operatorname{dist}(f,g)=\Pr_x[f(x)\ne g(x)]$ for uniform $x$, and the distance to a class is the minimum over all of its members; in particular $\delta_U(f)=\operatorname{dist}(f,C_U)$. The further objects are the Fourier weights $\operatorname{wt}(U)=\sum_{s\in U}\widehat f(s)^2$ and $\operatorname{wt}(\overline U)=\sum_{s\notin U}\widehat f(s)^2$, the real-valued spectral projection
--
--   $$
--   \Pi_Uf(x)=\sum_{s\in U}\widehat f(s)\chi_s(x),
--   $$
--
--   the annihilator $U^\perp=\{h:\langle u,h\rangle=0\text{ for all }u\in U\}$, and the uniform average $\mathbb E_{h\in U^\perp}[f(x+h)]$.
--
--   These objects are the language of the tester: $D_k$ is the property tested, and $C_U$ and the weights relate distance to Fourier mass outside a subspace.
--
--   **Formalization Note** The bit function `BoolFn n` is the primary object, because the XOR oracle adds that bit; `toSign` gives the $\{-1,1\}$-valued function used in every Fourier formula. Coefficients use the published `boolFourier`. The distance to a set is an infimum of finitely many values; the file proves that both constant functions lie in $C_U$ and in $D_k$, so these infima are attained minima over nonempty sets. $\Pi_U$ is defined spectrally and $\delta_U$ by Hamming distance, so that neither of the source's Lemmas 3.2 and 3.3 is true by definition.
-- source:
--   Kenny Chen, Exponential Quantum Advantage in Testing Fourier Dimensionality, September 2026 STOC 2027 submission #102 preprint, source.pdf SHA-256 afe3d00f3d3887de87812ce319a69c1fca5c95912047974553110aa755de4298, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/102.pdf, pp.10–13 and p.15, §2 Definitions 2.1–2.4, §2.1, §2.2, §3.1

import Definitions.Def_QAlgorithms_Defs_BooleanFourier

/-!
# Fourier dimension of Boolean functions: the classical model

Kenny Chen, *Exponential Quantum Advantage in Testing Fourier Dimensionality*, September 2026
STOC 2027 submission #102 preprint, §2.1 (pp.10–11), §2.2 (pp.12–13), §3 (p.15).
-/

namespace FourierDimTesting102.Quantum

open QAlgorithms

/-- §2, p.10: the domain `F₂ⁿ`, all `n`-bit vectors, with coordinatewise addition modulo 2. -/
abbrev V (n : ℕ) := Fin n → ZMod 2

/-- §2, p.10: a boolean function, recorded by its bit `b_f`, where `f(x) = (-1)^{b_f(x)}`. The bit
is what the XOR oracle of §2.2 adds; `toSign` is the source's `{-1,1}`-valued function. -/
abbrev BoolFn (n : ℕ) := V n → Bool

/-- The sign `(-1)^b`: bit `false` is `+1`, bit `true` is `-1`. -/
def signOf (b : Bool) : ℝ := if b then -1 else 1

/-- §2, p.10: the `{-1,1}`-valued function `f : F₂ⁿ → {-1,1}` with bit function `b_f`. -/
def toSign {n : ℕ} (f : BoolFn n) : V n → ℝ := fun x => signOf (f x)

/-- Definition 2.1, p.11: the character `χ_s(x) = (-1)^{⟨s,x⟩}`. -/
noncomputable def chi {n : ℕ} (s x : V n) : ℝ := (-1 : ℝ) ^ (s ⬝ᵥ x).val

/-- Definition 2.2, p.11: the Fourier coefficient `f̂(s) = 2^{-n} ∑_x f(x) χ_s(x)` of the
sign-valued function. -/
noncomputable def coeff {n : ℕ} (f : BoolFn n) (s : V n) : ℝ := boolFourier (toSign f) s

/-- Definition 2.3, p.11: the support of `f̂`, including frequency `0` when `f̂(0) ≠ 0`. -/
def fourierSupport {n : ℕ} (f : BoolFn n) : Set (V n) := {s | coeff f s ≠ 0}

/-- Definition 2.3, p.11: the `F₂`-span of the support of `f̂`. -/
def fourierSpan {n : ℕ} (f : BoolFn n) : Submodule (ZMod 2) (V n) :=
  Submodule.span (ZMod 2) (fourierSupport f)

/-- Definition 2.3, p.11: the Fourier dimension `dim(span(supp f̂))` over `F₂`. -/
noncomputable def fourierDim {n : ℕ} (f : BoolFn n) : ℕ :=
  Module.finrank (ZMod 2) (fourierSpan f)

/-- §2.1, p.11: `D_k`, all boolean functions of Fourier dimension at most `k`. -/
def Dk (n k : ℕ) : Set (BoolFn n) := {g | fourierDim g ≤ k}

/-- §2.1, p.11: `C_U = {g : supp(ĝ) ⊆ U}`, a set of boolean functions. -/
def CU {n : ℕ} (U : Submodule (ZMod 2) (V n)) : Set (BoolFn n) :=
  {g | fourierSupport g ⊆ U}

/-- Definition 2.4, p.12: `dist(f,g) = Pr_x[f(x) ≠ g(x)]`, `x` uniform on `F₂ⁿ`. -/
noncomputable def boolDist {n : ℕ} (f g : BoolFn n) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) / 2 ^ n

/-- The distance from `f` to a set of boolean functions, the smallest of the distances to its
members. Every set below is finite and nonempty (`CU_nonempty`, `Dk_nonempty`), so this is a
genuine minimum (`exists_boolDist_eq_distToSet`); on the empty set the value would be `0`. -/
noncomputable def distToSet {n : ℕ} (f : BoolFn n) (S : Set (BoolFn n)) : ℝ :=
  sInf (boolDist f '' S)

/-- §2.2, p.12: `δ_U(f) = dist(f, C_U)`. -/
noncomputable def deltaU {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) : ℝ :=
  distToSet f (CU U)

open Classical in
/-- §2.2, p.12: `wt(U) = ∑_{s ∈ U} f̂(s)²`. -/
noncomputable def wtIn {n : ℕ} (f : BoolFn n) (U : Submodule (ZMod 2) (V n)) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), coeff f s ^ 2

open Classical in
/-- §2.2, p.13: `wt(Ū) = ∑_{s ∉ U} f̂(s)²`. -/
noncomputable def wtOut {n : ℕ} (f : BoolFn n) (U : Submodule (ZMod 2) (V n)) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s ∉ U), coeff f s ^ 2

open Classical in
/-- §2.1, p.11: the spectral projection `Π_U f(x) = ∑_{s ∈ U} f̂(s) χ_s(x)`, a real-valued
function that need not be boolean. -/
noncomputable def proj {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) (x : V n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s ∈ U), coeff f s * chi s x

/-- §3.1, p.15: the annihilator `U^⊥ = {h : ⟨u,h⟩ = 0 for all u ∈ U}` for the `F₂` dot product. -/
def perp {n : ℕ} (U : Submodule (ZMod 2) (V n)) : Submodule (ZMod 2) (V n) where
  carrier := {h | ∀ u ∈ U, u ⬝ᵥ h = 0}
  add_mem' := fun ha hb u hu => by rw [dotProduct_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => dotProduct_zero u
  smul_mem' := fun c _ hh u hu => by rw [dotProduct_smul, hh u hu, smul_zero]

open Classical in
/-- §3.1, p.15: `E_{h ∈ U^⊥}[f(x+h)]`, the uniform average over the whole of `U^⊥`, which always
contains `0`. -/
noncomputable def cosetAverage {n : ℕ} (U : Submodule (ZMod 2) (V n)) (f : BoolFn n) (x : V n) :
    ℝ :=
  ((Finset.univ.filter (fun h => h ∈ perp U)).card : ℝ)⁻¹ *
    ∑ h ∈ Finset.univ.filter (fun h => h ∈ perp U), toSign f (x + h)

/-! ### Structural facts: the classes are nonempty, so `distToSet` is a minimum -/

theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℝ) ^ (a + b).val = (-1 : ℝ) ^ a.val * (-1 : ℝ) ^ b.val := by
  rw [ZMod.val_add, ← pow_add, ← neg_one_pow_eq_pow_mod_two]

theorem chi_add_right {n : ℕ} (s x y : V n) : chi s (x + y) = chi s x * chi s y := by
  simp only [chi, dotProduct_add, neg_one_pow_val_add]

theorem chi_add_left {n : ℕ} (s t x : V n) : chi (s + t) x = chi s x * chi t x := by
  simp only [chi, add_dotProduct, neg_one_pow_val_add]

theorem chi_comm {n : ℕ} (s x : V n) : chi s x = chi x s := by
  simp only [chi, dotProduct_comm]

theorem chi_mul_self {n : ℕ} (s x : V n) : chi s x * chi s x = 1 := by
  rw [← pow_two, chi, ← pow_mul, mul_comm, pow_mul]; simp

theorem sum_chi_eq_zero {n : ℕ} {s : V n} (hs : s ≠ 0) : ∑ x : V n, chi s x = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
  have hi1 : s i = 1 := by
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (s i) with h | h
    · exact absurd h hi
    · exact h
  have he : chi s (Pi.single i 1) = -1 := by
    have h1 : (1 : ZMod 2).val = 1 := rfl
    rw [chi, dotProduct_single, hi1, mul_one, h1, pow_one]
  have hshift : ∑ x : V n, chi s (x + Pi.single i 1) = ∑ x : V n, chi s x :=
    Equiv.sum_comp (Equiv.addRight (Pi.single i 1 : V n)) (chi s)
  have hneg : ∑ x : V n, chi s (x + Pi.single i 1) = -∑ x : V n, chi s x := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [chi_add_right, he, mul_neg, mul_one]
  exact self_eq_neg.mp (hshift.symm.trans hneg)

theorem coeff_const_false {n : ℕ} {s : V n} (hs : s ≠ 0) :
    coeff (fun _ => false) s = 0 := by
  have h := sum_chi_eq_zero hs
  simp only [chi] at h
  simp [coeff, boolFourier, toSign, signOf, h]

theorem coeff_const_true {n : ℕ} {s : V n} (hs : s ≠ 0) :
    coeff (fun _ => true) s = 0 := by
  have h := sum_chi_eq_zero hs
  simp only [chi] at h
  simp [coeff, boolFourier, toSign, signOf, h]

theorem const_mem_CU {n : ℕ} (U : Submodule (ZMod 2) (V n)) (b : Bool) :
    (fun _ => b : BoolFn n) ∈ CU U := by
  intro s hs
  by_cases h0 : s = 0
  · simp [h0]
  · cases b
    · exact absurd (coeff_const_false h0) hs
    · exact absurd (coeff_const_true h0) hs

theorem CU_nonempty {n : ℕ} (U : Submodule (ZMod 2) (V n)) : (CU U).Nonempty :=
  ⟨_, const_mem_CU U false⟩

theorem const_mem_Dk (n k : ℕ) (b : Bool) : (fun _ => b : BoolFn n) ∈ Dk n k := by
  have hle : fourierSpan (fun _ => b : BoolFn n) ≤ ⊥ :=
    Submodule.span_le.mpr (const_mem_CU ⊥ b)
  exact le_trans (Submodule.finrank_mono hle) (by simp)

theorem Dk_nonempty (n k : ℕ) : (Dk n k).Nonempty := ⟨_, const_mem_Dk n k false⟩

/-- On a nonempty set of boolean functions, `distToSet` is attained: it is the true minimum. -/
theorem exists_boolDist_eq_distToSet {n : ℕ} (f : BoolFn n) {S : Set (BoolFn n)}
    (hS : S.Nonempty) : ∃ g ∈ S, boolDist f g = distToSet f S := by
  have h := (hS.image (boolDist f)).csInf_mem ((Set.toFinite S).image _)
  obtain ⟨g, hg, hgd⟩ := h
  exact ⟨g, hg, hgd⟩

end FourierDimTesting102.Quantum


