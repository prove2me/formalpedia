-- Prove2me | Definitions.Def_RPB108_DNE27SourcePairing_Even
-- name    : RPB108_DNE27SourcePairing_Even
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-11T04:26:13.236859+00:00
-- url     : https://prove2.me/theorems/01069b26-08a3-48c1-85dd-9ec3496a888f
-- title:
--   DNE27 even actual inverse-source pairing
-- statement:
--   For a complex inner-product space, a continuous complex-linear map T, four actual source vectors and four complex coordinates, the inverse-source pairing is the inner product of source zero with T applied to the retained source combination. The same T is used in the completed columns in later theorems. Native definitions and exact data are preserved. Realization, row enclosures and inverse bounds for the original Weil form remain explicit caller obligations.
--
--   Approval/restoration note (2026-10-11): The user confirmed approval and merger of Weil PRs #1 and #2. The published source is now included in approved Weil/main at d2b758dfdd01b40887a3cb97524f29013c74c7ba. All 23 RPB108 component modules were checked byte-for-byte against the publication source. The record is restored within its existing conditional/exact-data scope; no original-form attachment or RH claim is added.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/DNE27SourcePairing.lean#L24-L27; source SHA256 498d343d111ed242d24172da2d719cf493eb78251dc2d20676f79374bbe10800. Compiler-derived skeleton subtraction; definitions unchanged.
--
--   Approved source promotion: Weil PR #2 was merged into main at d2b758dfdd01b40887a3cb97524f29013c74c7ba after user approval; source bytes match the original publication pin.

import Mathlib
import Definitions.Def_RPB108_DNE27RetainedEnergy_Even
import Definitions.Def_RPB108_DNE27NativePairing_Even
open scoped BigOperators
noncomputable section
namespace WeilDefect.RPB108

namespace DNE27Even





def inverseSourcePairing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (source : Fin 4 → E)
    (z : Fin 4 → ℂ) : ℂ :=
  inner ℂ (source 0) (T (∑ i : Fin 3, z i.succ • source i.succ))





end DNE27Even

namespace DNE27Odd











end DNE27Odd
end WeilDefect.RPB108


