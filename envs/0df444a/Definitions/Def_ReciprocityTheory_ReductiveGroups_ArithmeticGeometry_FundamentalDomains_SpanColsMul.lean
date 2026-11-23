-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:48.004922+00:00
-- url     : https://prove2.me/theorems/56886147-15c9-4695-bbfd-532a86199e96
-- title:
--   Span Cols Mul
-- statement:
--   Definitions and structural lemmas for Span Cols Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/SpanColsMul.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
def Am (u : Fin 2 → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin 2) ℂ :=
  Matrix.of fun a i => emb τ.1 (u i) a
noncomputable def Cm (u : Fin 2 → Fin r → E) (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (τ : X.Ψ) :
    Matrix (Fin 2) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (emb τ.1 (u k) l)
end Data
end ReciprocityTheory.ChartRestriction.G.FD


