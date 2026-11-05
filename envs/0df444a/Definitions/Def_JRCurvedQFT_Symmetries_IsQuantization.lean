-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_IsQuantization
-- name    : JRCurvedQFT_Symmetries_IsQuantization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:19.913467+00:00
-- url     : https://prove2.me/theorems/313ae30a-407d-47b4-bc34-d23aa6c342e4
-- title:
--   Quantization of $T\restriction\mathscr D_0$ with domain $\hat{\mathscr D}_0$
-- statement:
--   An operator $\hat T$ on $\mathcal H$ is the **quantization** of $T\restriction\mathscr D_0$ if its domain is $\hat{\mathscr D}_0=\Pi(\mathscr D_0)$ and $\hat T\hat A=\widehat{TA}$ for $A\in\mathscr D_0$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, (3.3), p. 4; Theorem 3.3, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `That` is the **quantization** of `T↾D₀` with domain `D̂₀ = Π(D₀)`: `T̂ Π(A) = Π(T A)` for `A ∈ D₀`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, (3.3), p. 4: "We wish to define the quantization T̂ with the putative domain D̂₀ by
T̂ Â = (TA)^". -/
def IsQuantization (r : ReflectionData E) (T : E →ₗ.[ℂ] E) (D0 : Submodule ℂ E)
    (That : OS r →ₗ.[ℂ] OS r) : Prop :=
  That.domain = (D0.submoduleOf r.plus).map (osQ r) ∧
  ∀ (A : r.plus), (A : E) ∈ D0 → ∀ (hT : (A : E) ∈ T.domain) (hTA : T ⟨A, hT⟩ ∈ r.plus)
    (h : osQ r A ∈ That.domain), That ⟨osQ r A, h⟩ = osQ r ⟨T ⟨A, hT⟩, hTA⟩

end JRCurvedQFT.Symmetries


