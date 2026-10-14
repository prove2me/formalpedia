-- Prove2me | Definitions.Def_Zeta5_SourceAtoms
-- name    : Zeta5_SourceAtoms
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T00:33:45.583978+00:00
-- url     : https://prove2.me/theorems/a000ee1b-9fad-4f95-8d10-274b7970a323
-- title:
--   Zeta5: the atoms of the configuration energy (circles and arcsine curves)
-- statement:
--   The atoms of the configuration energy of Section 6. For a configuration $t : \mathrm{Fin}\,h \to \mathbb{R}$ and a radius $\varepsilon > 0$:
--
--   * `Idx h = Fin h ⊕ Fin 16`, the index type of the atoms;* the weights `atomS h K`: $1/K$ on the circles and $-c_j$ on the sixteen arcsine curves of Table 1;* the arcsine curve `arcCurve m r`: $\theta \mapsto m + r\cos\theta$;* the curves `atomγ t ε`: the circles $\theta \mapsto t_i + \varepsilon e^{i\theta}$ (for $i < h$) and the sixteen arcsine curves $\theta \mapsto m_j + r_j\cos\theta$;* the pair integral of a kernel, `pairInt γ f k l = ∫₀^{2π}∫₀^{2π} f(γ_k θ)(γ_l φ) dφ dθ`;* the energy of the signed combination of atoms, `energy s γ f = ∑_{k,l} s_k s_l pairInt γ f k l`;* the pair integrals of the logarithmic kernel, `Plog t ε k l = pairInt (atomγ t ε) (fun z w => log ‖z-w‖) k l`.
--
--   These are the objects in which the raw configuration inequality `energy_raw` and the four block inequalities (A)–(D) of `Apery/EnergyBlocks.lean` are stated.
--
--   **Formalization Note** `Idx` is an `abbrev`; the rest are `noncomputable def`s in the `Apery` namespace, verbatim from the source modules.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/ArcsineAtoms.lean#L19, Apery/ZeroMass.lean#L27-L33, Apery/EnergyAtoms.lean#L44-L55, Apery/EnergyBlocks.lean#L19-L21

import Mathlib
import Definitions.Def_Zeta5_SourceMeasure
import Definitions.Def_Zeta5_SourceEnergy

/-!
# The atoms of the configuration energy

For a configuration `t : Fin h → ℝ` and a radius `ε > 0`, the atoms are the circles of
radius `ε` around the `t i` (weights `1/K`) and the sixteen arcsine curves (weights `-c_j`),
together with the pair integrals and the energy functional of the logarithmic kernel.

* `Idx h = Fin h ⊕ Fin 16`: the index type of the atoms;
* `atomS h K`: the weights `1/K` on the circles and `-c_j` on the arcsine curves;
* `arcCurve m r θ = m + r cos θ`: the arcsine curve;
* `atomγ t ε`: the curves (circles of radius `ε` around the `t i`, and the sixteen arcsine
  curves `θ ↦ m_j + r_j cos θ`);
* `pairInt γ f k l = ∫₀^{2π} ∫₀^{2π} f (γ_k θ) (γ_l φ) dφ dθ`;
* `energy s γ f = ∑_{k,l} s_k s_l pairInt γ f k l`;
* `Plog t ε k l = pairInt (atomγ t ε) (fun z w => log ‖z - w‖) k l`.

Source: mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/ArcsineAtoms.lean` line 19, `Apery/ZeroMass.lean` lines 27–33,
`Apery/EnergyAtoms.lean` lines 44–55, `Apery/EnergyBlocks.lean` lines 19–21.
-/

open MeasureTheory Set Real

namespace Apery

/-- The index type of the atoms: the `h` circles and the sixteen arcsine curves. -/
abbrev Idx (h : ℕ) := Fin h ⊕ Fin 16

/-- The weights of the atoms: `1/K` for the circles, `-c_j` for the arcsine curves. -/
noncomputable def atomS (h : ℕ) (K : ℝ) : Idx h → ℝ
  | Sum.inl _ => 1 / K
  | Sum.inr j => -cρ (j + 1)

/-- The arcsine curve `θ ↦ m + r cos θ` on the real line. -/
noncomputable def arcCurve (m r : ℝ) (θ : ℝ) : ℂ := ((m + r * Real.cos θ : ℝ) : ℂ)

/-- The curves of the atoms: circles of radius `ε` around the `t i`, and the sixteen arcsine
curves of Table 1. -/
noncomputable def atomγ {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) : Idx h → ℝ → ℂ
  | Sum.inl i => circleMap (t i) ε
  | Sum.inr j => arcCurve (mρ (j + 1)) (rρ (j + 1))

variable {ι : Type*}

/-- Double integral of a kernel against two atoms. -/
noncomputable def pairInt (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) (k l : ι) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π, f (γ k θ) (γ l φ)

/-- The energy of the signed combination of atoms. -/
noncomputable def energy [Fintype ι] (s : ι → ℝ) (γ : ι → ℝ → ℂ) (f : ℂ → ℂ → ℝ) : ℝ :=
  ∑ k, ∑ l, s k * s l * pairInt γ f k l

/-- The pair integrals of the logarithmic kernel for the configuration atoms. -/
noncomputable def Plog {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k l : Idx h) : ℝ :=
  pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) k l

end Apery


