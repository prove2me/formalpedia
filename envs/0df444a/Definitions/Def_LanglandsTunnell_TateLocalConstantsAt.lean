-- Prove2me | Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
-- name    : LanglandsTunnell_TateLocalConstantsAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/40883c57-5f39-5548-aa31-cfb56846c052
-- title:
--   Local conductor exponents, L-factors and ε-factors at a finite place
-- statement:
--   Throughout, $K$ is a number field and $v$ a height-one prime of $\mathcal{O}_K$, with completion $K_v$ written `v.adicCompletion K` and valuation `Valued.v` taking values in $\mathbb{Z}\cup\{0\}$ written multiplicatively. For $n:\mathbb{N}$, `higherUnitsAt K v n` is the set of units $u\in K_v^\times$ with $|u|=1$ and, when $n>0$, $|u-1|\le \exp(-n)$; for $n=0$ the second condition is vacuous, so this is the full unit group of the valuation ring. Accompanying lemmas record the membership criterion, the case $n=0$, that $1$ lies in every `higherUnitsAt K v n`, and that the family is antitone in $n$.
--
--   `HasConductorExponentAt K v χ c`, for a homomorphism $\chi : K_v^\times\to\mathbb{C}^\times$ and $c:\mathbb{N}$, is the conjunction: $\chi$ is trivial on `higherUnitsAt K v c`, and for every $m<c$ there is an element of `higherUnitsAt K v m` on which $\chi$ is non-trivial. It holds for $c=0$ exactly when $\chi$ kills all units of valuation $1$; such a $c$ is unique; the trivial character has exponent $0$ and no exponent $c+1$. The total function `conductorExponentAt K v χ` is the infimum of the set of such $c$ (hence $0$ when that set is empty), and equals $c$ whenever `HasConductorExponentAt K v χ c` holds.
--
--   `localLFactorAt K v χ s` is $(1-\chi(\varpi_v)\,(N v)^{-s})^{-1}$ if `HasConductorExponentAt K v χ 0` holds, and $1$ otherwise; here $\varpi_v$ is the uniformiser unit `uniformizerUnit K v` and $Nv=$`Ideal.absNorm v.asIdeal`. Inversion is Lean's total inverse, so the value is $0$ at a pole. Finally, for a measure $\mu$ and additive character $\psi$ on $K_v$ and a test function $f$, `localEpsilonAt K v μ ψ f χ s` is defined as `localGammaAt μ ψ f χ s` multiplied by `localLFactorAt K v χ s` and divided by `localLFactorAt K v χ⁻¹ (1-s)`, where `localGammaAt` is the ratio of Tate local zeta integrals $Z(\hat f,\chi^{-1},1-s)/Z(f,\chi,s)$. It equals the $\gamma$-factor when $\chi$ has no conductor exponent $0$, and vanishes when the zeta integral $Z(f,\chi,s)$ vanishes.
--
--   **Relation to Mathlib.** Mathlib provides the valuation-theoretic framework (`HeightOneSpectrum.adicCompletion`, `Valued.v`, `Ideal.absNorm`) but no local conductor exponents or local $L$- and $\varepsilon$-factors; these are the project's own definitions, built on its own Tate local zeta integral and $\gamma$-ratio.
--
--   **Where it is used.** These local constants feed the analytic side of the Langlands–Tunnell input to modularity: conductor exponents govern the level of the associated automorphic object, and the local $L$- and $\varepsilon$-factors are the building blocks of the Euler products and functional equations used there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}

theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

theorem one_mem_higherUnitsAt (n : ℕ) : (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))

def HasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnitsAt K v c, χ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnitsAt K v m, χ u ≠ 1

theorem hasConductorExponentAt_zero_iff {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    HasConductorExponentAt K v χ 0 ↔
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ u = 1 := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnitsAt_zero_iff K v).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnitsAt_zero_iff K v).mp hu),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

theorem hasConductorExponentAt_unique {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasConductorExponentAt K v χ c) (h' : HasConductorExponentAt K v χ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

theorem hasConductorExponentAt_one_zero :
    HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ _ => rfl

theorem not_hasConductorExponentAt_one_succ (c : ℕ) :
    ¬ HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

def conductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {c | HasConductorExponentAt K v χ c}

theorem conductorExponentAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : HasConductorExponentAt K v χ c) : conductorExponentAt K v χ = c := by
  have hmem : c ∈ {c' | HasConductorExponentAt K v χ c'} := h
  have hle : conductorExponentAt K v χ ≤ c := Nat.sInf_le hmem
  have hge : c ≤ conductorExponentAt K v χ := by
    have hne : {c' | HasConductorExponentAt K v χ c'}.Nonempty := ⟨c, h⟩
    have hmemInf := Nat.sInf_mem hne
    exact (hasConductorExponentAt_unique K v hmemInf h).ge
  omega

@[simp] theorem conductorExponentAt_one :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v (hasConductorExponentAt_one_zero K v)

open Classical in

def localLFactorAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

theorem localLFactorAt_of_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s
      = (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt, if_pos hχ]

theorem localLFactorAt_of_not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) : localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, if_neg hχ]

theorem localLFactorAt_one (s : ℂ) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s
      = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v (hasConductorExponentAt_one_zero K v),
    MonoidHom.one_apply, Units.val_one, one_mul]

section Epsilon

variable [MeasurableSpace (v.adicCompletion K)]

def localEpsilonAt (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

theorem localEpsilonAt_def (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s
      = localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s) :=
  rfl

theorem localEpsilonAt_of_not_hasConductorExponentAt_zero (μ : Measure (v.adicCompletion K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s = localGammaAt μ ψ f χ s := by
  have hχ' : ¬ HasConductorExponentAt K v χ⁻¹ 0 := fun h => hχ <| by
    rw [hasConductorExponentAt_zero_iff] at h ⊢
    intro u hu
    have := h u hu
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  rw [localEpsilonAt, localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ', mul_one, div_one]

theorem localEpsilonAt_eq_zero_of_localZeta_eq_zero {μ : Measure (v.adicCompletion K)}
    {ψ : AddChar (v.adicCompletion K) ℂ} {f : v.adicCompletion K → ℂ}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f χ s = 0) :
    localEpsilonAt K v μ ψ f χ s = 0 := by
  rw [localEpsilonAt, localGammaAt_eq_zero_of_localZeta_eq_zero h, zero_mul, zero_div]

end Epsilon

end LanglandsTunnell.TateLocal

end


