-- Prove2me | Definitions.Def_PowerSeries_FormalHeckeOperators
-- name    : PowerSeries_FormalHeckeOperators
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/49c0982f-4ae2-576b-9df0-52ffc27da38d
-- title:
--   Formal Hecke operators on power series
-- statement:
--   Over a commutative ring $R$ this module defines three $R$-linear endomorphisms of the power series ring $R[\![X]\!]$, modelling the action of Hecke operators on $q$-expansions coefficient by coefficient. For a natural number $\ell$, [`PowerSeries.heckeU`](../def/PowerSeries_FormalHeckeOperators.html#L11) is the map sending $f$ to the series whose $n$-th coefficient is the $(\ell n)$-th coefficient of $f$; thus $U_\ell(\sum a_n X^n) = \sum a_{\ell n} X^n$. [`PowerSeries.heckeV`](../def/PowerSeries_FormalHeckeOperators.html#L20) sends $f$ to the series whose $n$-th coefficient is the $(n/\ell)$-th coefficient of $f$ when $\ell \mid n$ and $0$ otherwise; thus $V_\ell(\sum a_n X^n) = \sum a_n X^{\ell n}$. Both are bundled as $R$-linear maps, additivity and $R$-homogeneity being immediate from the coefficientwise description. Finally, for $\ell$ and a weight $k$, [`PowerSeries.heckeT`](../def/PowerSeries_FormalHeckeOperators.html#L33) is defined as the $R$-linear combination $U_\ell + \ell^{k-1} V_\ell$, where $\ell^{k-1}$ means the $(k-1)$-st power of the image of $\ell$ in $R$ and $k-1$ is truncated natural subtraction (so the scalar is $1$ when $k = 0$ or $k = 1$).
--
--   The accompanying coefficient lemmas `coeff_heckeU`, `coeff_heckeV` and `coeff_heckeT` record these descriptions as simp-normal identities, the last reading $a_n(T_\ell^{(k)} f) = a_{\ell n}(f) + \ell^{k-1}\cdot c_n$, where $c_n = a_{n/\ell}(f)$ if $\ell \mid n$ and $c_n = 0$ otherwise. The lemma `heckeU_heckeV` states that for $\ell \neq 0$ one has $U_\ell(V_\ell f) = f$ for every $f$, i.e. $V_\ell$ is a right inverse of $U_\ell$. No assumption that $\ell$ is prime, nor any relation to modular forms, is imposed: these are purely formal operations on coefficient sequences.
--
--   **Relation to Mathlib.** Mathlib has no Hecke operators on formal power series; these are the project's own definitions, built on Mathlib's `PowerSeries` and its `coeff`/`mk` interface.
--
--   **Where it is used.** These operators give the $q$-expansion-level form of the Hecke action, so that statements about modular forms and their eigenvalues — normalised eigenform criteria, congruences between coefficients, and the Hecke action used in the level- and weight-lowering arguments — can be phrased and manipulated entirely in terms of coefficient sequences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PowerSeries_FormalHeckeOperators.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace PowerSeries

variable {R : Type*} [CommRing R]

def heckeU (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => coeff (ℓ * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

@[simp] lemma coeff_heckeU (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeU ℓ f) = coeff (ℓ * n) f := by
  simp [heckeU]

def heckeV (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => if ℓ ∣ n then coeff (n / ℓ) f else 0
  map_add' f g := by ext n; by_cases h : ℓ ∣ n <;> simp [h]
  map_smul' c f := by ext n; by_cases h : ℓ ∣ n <;> simp [h]

@[simp] lemma coeff_heckeV (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeV ℓ f) = if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeV]

lemma heckeU_heckeV (ℓ : ℕ) (hℓ : ℓ ≠ 0) (f : R⟦X⟧) : heckeU ℓ (heckeV ℓ f) = f := by
  ext n
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hℓ), Dvd.intro n rfl]

def heckeT (ℓ k : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  heckeU ℓ + (ℓ : R) ^ (k - 1) • heckeV ℓ

lemma coeff_heckeT (ℓ k n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeT ℓ k f) =
      coeff (ℓ * n) f + (ℓ : R) ^ (k - 1) * if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeT]

end PowerSeries

end


