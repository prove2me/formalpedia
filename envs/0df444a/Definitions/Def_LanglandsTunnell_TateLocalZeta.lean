-- Prove2me | Definitions.Def_LanglandsTunnell_TateLocalZeta
-- name    : LanglandsTunnell_TateLocalZeta
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/fb28bd2e-428d-5626-a7c5-6d5a660289e8
-- title:
--   Carriers for Tate's local theory: modulus, zeta integrals, gamma ratio
-- statement:
--   Throughout, $K$ is a field; for the modulus and the zeta integral it also carries a topology making it a topological ring which is locally compact, and for the integrals a measurable space structure. `modulus a : ℝ≥0` is defined to be $0$ when $a = 0$ and otherwise Mathlib's `distribHaarChar K` evaluated at the unit determined by $a$, i.e. the factor by which multiplication by $a$ scales an additive Haar measure of $K$; the accompanying lemmas record $|0| = 0$, the value on units, strict positivity and non-vanishing for $a \neq 0$, $|1| = 1$ and multiplicativity $|ab| = |a||b|$. `IsSchwartzBruhat f`, for $f : K \to \mathbb{C}$ on a topological space $K$, is the conjunction of `IsLocallyConstant f` and `HasCompactSupport f`; the zero function satisfies it, and so does $c \cdot \mathbf{1}_U$ for any clopen compact $U \subseteq K$ and any $c \in \mathbb{C}$. `tateFourier ψ μ f y` $= \int_K f(x)\,\psi(xy)\,d\mu(x)$ for an additive character $\psi : K \to \mathbb{C}$ and a measure $\mu$, defined for arbitrary $f$ (the zero function transforms to zero). `charExt χ x` extends a homomorphism $\chi : K^\times \to \mathbb{C}^\times$ to all of $K$ by the value $0$ at $0$, with the evident lemmas at units and for the trivial character. `mulMeasure μ` is $\mu$ restricted to $K \setminus \{0\}$ and given density $x \mapsto (\text{modulus } x)^{-1}$ in $\mathbb{R}_{\geq 0}^\infty$, and `localZeta μ f χ s` is $\int f(x)\,\chi(x)\,|x|^{s}\,d(\text{mulMeasure } \mu)(x)$, with $|x|^s$ formed from the real number `modulus x` viewed in $\mathbb{C}$; it vanishes on $f = 0$. Finally `localGammaAt μ ψ f₀ χ s` is the quotient $Z(\widehat{f_0}, \chi^{-1}, 1-s) / Z(f_0, \chi, s)$ of two such integrals, formed at one chosen test function $f_0$; as a Lean division it is $0$ whenever the denominator is $0$, which is recorded as a lemma. Independence of the choice of $f_0$, i.e. the local functional equation, is not part of these definitions but a statement about them.
--
--   **Relation to Mathlib.** `modulus` is packaged from Mathlib's `distribHaarChar`, extended by the value $0$ at $0$; the remaining notions (the non-archimedean Schwartz–Bruhat condition, the Fourier transform against Tate's kernel $\psi(xy)$, the multiplicative measure $|x|^{-1}d\mu$, the local zeta integral and the gamma ratio) have no Mathlib counterparts and are the project's own.
--
--   **Where it is used.** These are the carriers for the local analytic input to the Langlands–Tunnell theorem, which supplies the modularity of the residual mod $3$ representation used to start the modularity-lifting argument for Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_TateLocalZeta.lean

import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.LocallyConstant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell.TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

def modulus (a : K) : ℝ≥0 := by
  classical exact if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

@[simp] theorem modulus_zero : modulus (0 : K) = 0 := by
  simp [modulus]

theorem modulus_of_ne_zero {a : K} (h : a ≠ 0) : modulus a = distribHaarChar K (Units.mk0 a h) := by
  simp [modulus, h]

@[simp] theorem modulus_coe_units (u : Kˣ) : modulus (u : K) = distribHaarChar K u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

theorem modulus_pos {a : K} (h : a ≠ 0) : 0 < modulus a := by
  rw [modulus_of_ne_zero h]
  exact distribHaarChar_pos

theorem modulus_ne_zero {a : K} (h : a ≠ 0) : modulus a ≠ 0 :=
  (modulus_pos h).ne'

@[simp] theorem modulus_one : modulus (1 : K) = 1 := by
  rw [modulus_of_ne_zero one_ne_zero, Units.mk0_one, map_one]

theorem modulus_mul (a b : K) : modulus (a * b) = modulus a * modulus b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [modulus_of_ne_zero (mul_ne_zero ha hb), modulus_of_ne_zero ha, modulus_of_ne_zero hb,
    ← map_mul]
  congr 1
  exact Units.ext rfl

end Modulus

section TestFunctions

variable {K : Type*} [TopologicalSpace K]

def IsSchwartzBruhat (f : K → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

theorem IsSchwartzBruhat.zero : IsSchwartzBruhat (0 : K → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem IsSchwartzBruhat.indicator_const {U : Set K} (hU : IsClopen U) (hUc : IsCompact U)
    (c : ℂ) : IsSchwartzBruhat (U.indicator fun _ => c) := by
  refine ⟨?_, ?_⟩
  · intro s
    classical
    have : (U.indicator fun _ => c) ⁻¹' s =
        (if c ∈ s then U else ∅) ∪ (if (0 : ℂ) ∈ s then Uᶜ else ∅) := by
      ext x
      by_cases hx : x ∈ U <;> by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
        simp [Set.indicator, hx, hc, h0]
    rw [this]
    refine IsOpen.union ?_ ?_
    · split_ifs
      · exact hU.isOpen
      · exact isOpen_empty
    · split_ifs
      · exact hU.compl.isOpen
      · exact isOpen_empty
  · exact HasCompactSupport.intro' hUc hU.isClosed fun x hx => Set.indicator_of_notMem hx _

end TestFunctions

section Fourier

variable {K : Type*} [Field K] [MeasurableSpace K]

def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) : ℂ :=
  ∫ x, f x * ψ (x * y) ∂μ

theorem tateFourier_zero_fun (ψ : AddChar K ℂ) (μ : Measure K) :
    tateFourier ψ μ (0 : K → ℂ) = 0 := by
  funext y
  simp [tateFourier]

end Fourier

section Characters

variable {K : Type*} [Field K]

def charExt (χ : Kˣ →* ℂˣ) (x : K) : ℂ := by
  classical exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

@[simp] theorem charExt_zero (χ : Kˣ →* ℂˣ) : charExt χ (0 : K) = 0 := by
  simp [charExt]

theorem charExt_of_ne_zero (χ : Kˣ →* ℂˣ) {x : K} (h : x ≠ 0) :
    charExt χ x = χ (Units.mk0 x h) := by
  simp [charExt, h]

@[simp] theorem charExt_coe_units (χ : Kˣ →* ℂˣ) (u : Kˣ) : charExt χ (u : K) = χ u := by
  rw [charExt_of_ne_zero χ u.ne_zero, Units.mk0_val]

theorem charExt_one_of_ne_zero {x : K} (h : x ≠ 0) : charExt (1 : Kˣ →* ℂˣ) x = 1 := by
  rw [charExt_of_ne_zero _ h, MonoidHom.one_apply, Units.val_one]

end Characters

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

def mulMeasure (μ : Measure K) : Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹

def localZeta (μ : Measure K) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)

theorem localZeta_zero_fun (μ : Measure K) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (0 : K → ℂ) χ s = 0 := by
  simp [localZeta]

def localGammaAt (μ : Measure K) (ψ : AddChar K ℂ) (f₀ : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s

theorem localGammaAt_eq_zero_of_localZeta_eq_zero {μ : Measure K} {ψ : AddChar K ℂ} {f₀ : K → ℂ}
    {χ : Kˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f₀ χ s = 0) : localGammaAt μ ψ f₀ χ s = 0 := by
  simp [localGammaAt, h]

end Zeta

end LanglandsTunnell.TateLocal

end


