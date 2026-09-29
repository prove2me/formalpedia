-- Prove2me | Definitions.Def_ModularCurve_WeierstrassLevelCarrier
-- name    : ModularCurve_WeierstrassLevelCarrier
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4ce66da5-3b61-580a-8ff4-09740f311c14
-- title:
--   Kernel polynomials of cyclic N-subgroups on Weierstrass models
-- statement:
--   Over a commutative ring $T$ with a Weierstrass curve $W$, the module introduces the currency for recording a cyclic level-$N$ structure as a polynomial in the $x$-coordinate. First, `smulNumerator` takes $a,d \in \mathbb{N}$ and $h \in T[X]$ to $\sum_{i=0}^{d} h_i\,\Phi_a^{\,i}\,(\Psi^{\mathrm{sq}}_a)^{\,d-i}$, where $h_i$ is the $i$-th coefficient of $h$ and $\Phi_a$, $\Psi^{\mathrm{sq}}_a$ are the division-polynomial numerator and denominator of $x([a]P)$; this is the numerator obtained from $h$ by substituting $x \mapsto \Phi_a/\Psi^{\mathrm{sq}}_a$ and clearing denominators, homogenised to degree $d$. Second, `IsCyclicKernel N h` is a four-field predicate on $h \in T[X]$: the natural degree of $h$ is at most $(N-1)/2$; the coefficient of $h$ in degree $(N-1)/2$ equals $1$; $h$ divides `preΨ N`, the $N$-th division polynomial in $x$; and $h$ divides `smulNumerator a ((N-1)/2) h` for every $a$ with $2 \le a \le (N-1)/2$. Thus $h$ is monic of degree exactly $(N-1)/2$ (recorded as `IsCyclicKernel.monic`), its roots lie among the $x$-coordinates of $N$-torsion points, and the set of those roots is stable under all multiplications $[a]$ — the defining conditions for $h$ to be the kernel polynomial $\prod (x - x(P))$ of a cyclic subgroup of order $N$, with no generating section required.
--
--   The datum is transported along a ring homomorphism $f : T \to T'$: `smulNumerator_map` identifies the construction for the base-changed curve applied to $h$ mapped by $f$ with the image of `smulNumerator`, and `IsCyclicKernel.map` transports all four fields. `kernelVariableChange` is the accompanying operation on polynomials for a variable change $C$ with parameters $u, r$, namely $u^{-2\deg h}\,h(u^2 X + r)$. Finally, `jOfUnit` gives the $j$-invariant of $W$ from a witness that $\Delta$ is a unit rather than from an `IsElliptic` instance; it agrees with `j` when such an instance is present, commutes with ring maps, is invariant under variable changes, and the unit property of $\Delta$ is itself shown to be preserved by base change and by variable changes.
--
--   **Relation to Mathlib.** Mathlib supplies the Weierstrass curve, its division polynomials `preΨ`, `Φ`, `ΨSq`, variable changes, and the $j$-invariant of an `IsElliptic` curve; `smulNumerator`, `IsCyclicKernel`, `kernelVariableChange` and `jOfUnit` are the project's own additions, the last being a packaging of Mathlib's `j` that takes the unit-discriminant witness as an explicit argument.
--
--   **Where it is used.** These definitions provide the carrier-level description of a $\Gamma_0(N)$-structure on an elliptic curve given by a Weierstrass model over an arbitrary base ring, a cyclic subgroup of order $N$ being encoded by its kernel polynomial in $x$ rather than by a generator. They are used throughout the tree's treatment of modular curves with $\Gamma_0(N)$-level structure and of the associated moduli descriptions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_WeierstrassLevelCarrier.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type*} [CommRing T] (W : WeierstrassCurve T)

def smulNumerator (a d : ℕ) (h : T[X]) : T[X] :=
  ∑ i ∈ Finset.range (d + 1), C (h.coeff i) * W.Φ a ^ i * W.ΨSq a ^ (d - i)

structure IsCyclicKernel (N : ℕ) (h : T[X]) : Prop where

  natDegree_le : h.natDegree ≤ (N - 1) / 2

  coeff_eq_one : h.coeff ((N - 1) / 2) = 1

  dvd_preΨ : h ∣ W.preΨ N

  dvd_smulNumerator : ∀ a : ℕ, 2 ≤ a → a ≤ (N - 1) / 2 → h ∣ W.smulNumerator a ((N - 1) / 2) h

theorem IsCyclicKernel.monic {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) : h.Monic :=
  Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hh.natDegree_le hh.coeff_eq_one

section Map

variable {T' : Type*} [CommRing T'] (f : T →+* T')

theorem smulNumerator_map (a d : ℕ) (h : T[X]) :
    (W.map f).smulNumerator a d (h.map f) = (W.smulNumerator a d h).map f := by
  simp only [smulNumerator, Polynomial.coeff_map, WeierstrassCurve.map_Φ,
    WeierstrassCurve.map_ΨSq, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C]

theorem IsCyclicKernel.map {N : ℕ} {h : T[X]} (hh : W.IsCyclicKernel N h) :
    (W.map f).IsCyclicKernel N (h.map f) where
  natDegree_le := (Polynomial.natDegree_map_le).trans hh.natDegree_le
  coeff_eq_one := by rw [Polynomial.coeff_map, hh.coeff_eq_one, map_one]
  dvd_preΨ := by rw [WeierstrassCurve.map_preΨ]; exact Polynomial.map_dvd f hh.dvd_preΨ
  dvd_smulNumerator := fun a ha ha' => by
    rw [W.smulNumerator_map f]; exact Polynomial.map_dvd f (hh.dvd_smulNumerator a ha ha')

end Map

def kernelVariableChange (C : VariableChange T) (h : T[X]) : T[X] :=
  Polynomial.C (((C.u⁻¹ : Tˣ) : T) ^ (2 * h.natDegree)) * h.comp (Polynomial.C ((C.u : Tˣ) : T) ^ 2 * X + Polynomial.C C.r)

def jOfUnit (hΔ : IsUnit W.Δ) : T :=
  haveI : W.IsElliptic := ⟨hΔ⟩
  W.j

theorem jOfUnit_eq_j [W.IsElliptic] (hΔ : IsUnit W.Δ) : W.jOfUnit hΔ = W.j := rfl

theorem jOfUnit_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (W.map f).Δ) :
    (W.map f).jOfUnit hΔ' = f (W.jOfUnit hΔ) := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.map_j f

theorem jOfUnit_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) (hΔ' : IsUnit (C • W).Δ) :
    (C • W).jOfUnit hΔ' = W.jOfUnit hΔ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact W.variableChange_j C

theorem isUnit_Δ_map {T' : Type*} [CommRing T'] (f : T →+* T') (hΔ : IsUnit W.Δ) : IsUnit (W.map f).Δ := by
  rw [W.map_Δ]; exact hΔ.map f

theorem isUnit_Δ_variableChange (C : VariableChange T) (hΔ : IsUnit W.Δ) : IsUnit (C • W).Δ := by
  haveI : W.IsElliptic := ⟨hΔ⟩
  exact (C • W).isUnit_Δ

end WeierstrassCurve

end


