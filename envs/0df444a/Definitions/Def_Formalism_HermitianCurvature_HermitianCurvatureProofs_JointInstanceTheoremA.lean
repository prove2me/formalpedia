-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:55.272246+00:00
-- url     : https://prove2.me/theorems/08cec035-b244-48a2-890e-e4be79d9aa17
-- title:
--   Joint Instance Theorem A
-- statement:
--   Definitions and structural lemmas for Joint Instance Theorem A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
namespace Formalism.FourierDecayAlt.P.Jx7
section frames
end frames
section sizes
open scoped nonZeroDivisors
section Gl
variable {ι : Type} [Fintype ι] (G : Sz.Glob ι) (C : ℝ) (de de' : ℕ → ℝ) (T T' : ℝ) (l : ℕ)
noncomputable def sp (p : Prop) [Decidable p] (w : ι) : ℝ :=
  if p then G.cutSupLong de de' T T' l w else G.supI de de' T T' l w
end Gl
end sizes
section sums
open scoped nonZeroDivisors
end sums
section positivity
end positivity
section main
open scoped ComplexOrder
end main
section kernels
open scoped ComplexOrder ComplexConjugate Matrix
section psd
variable {α : Type} {F : Finset α}
end psd
section schur
variable {α : Type} {F : Finset α}
end schur
end kernels
end Formalism.FourierDecayAlt.P.Jx7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


