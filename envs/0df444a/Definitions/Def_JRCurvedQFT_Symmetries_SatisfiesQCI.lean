-- Prove2me | Definitions.Def_JRCurvedQFT_Symmetries_SatisfiesQCI
-- name    : JRCurvedQFT_Symmetries_SatisfiesQCI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:16.279708+00:00
-- url     : https://prove2.me/theorems/14357e11-c658-4f0f-832d-1e826e05eed5
-- title:
--   Quantization Condition I
-- statement:
--   The operator $T$ satisfies **QC-I** with subdomain $\mathscr D_0$ if:
--
--   1. $T$ has a domain dense in $\mathcal E$;
--   2. $\mathscr D_0\subset\mathcal E_+\cap D(T)\cap D(T^+)$ and $\hat{\mathscr D}_0\subset\mathcal H$ is dense;
--   3. $T$ and $T^+$ both map $\mathscr D_0$ into $\mathcal E_+$.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries, arXiv:0704.0052v1, Definition 3.2, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92
import Definitions.Def_JRCurvedQFT_Symmetries_plusOp

open scoped Manifold ContDiff ENNReal Topology InnerProductSpace
open Bundle MeasureTheory
open QAlgorithms.Papers.Independent.Intakethird100.P92

namespace JRCurvedQFT.Symmetries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Quantization Condition I** for `T` with subdomain `D₀`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. II. Spacetime Symmetries*, arXiv:0704.0052v1, Definition 3.2, p. 4: "The operator T satisfies QC-I if: i. The operator T has a domain D(T)
dense in E. ii. There is a subdomain D₀ ⊂ E₊ ∩ D(T) ∩ D(T⁺), for which D̂₀ ⊂ ℋ is dense. iii. The
transformations T and T⁺ both map D₀ into E₊."

**Formalization Note** `D₀` is a parameter of the condition rather than existentially quantified, so
that Theorem 3.3 can speak of it. -/
structure SatisfiesQCI (r : ReflectionData E) (T : E →ₗ.[ℂ] E) (D0 : Submodule ℂ E) : Prop where
  dense_domain : Dense (T.domain : Set E)
  le_plus : D0 ≤ r.plus
  le_domain : D0 ≤ T.domain
  le_plus_domain : D0 ≤ (plusOp r T).domain
  dense_hat : Dense (((D0.submoduleOf r.plus).map (osQ r) : Submodule ℂ (OS r)) : Set (OS r))
  maps_T : ∀ x : T.domain, (x : E) ∈ D0 → T x ∈ r.plus
  maps_plus : ∀ x : (plusOp r T).domain, (x : E) ∈ D0 → plusOp r T x ∈ r.plus

end JRCurvedQFT.Symmetries


