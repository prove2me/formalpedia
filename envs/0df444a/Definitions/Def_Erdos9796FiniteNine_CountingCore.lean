-- Prove2me | Definitions.Def_Erdos9796FiniteNine_CountingCore
-- name    : Erdos9796FiniteNine_CountingCore
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-09T06:30:10.532006+00:00
-- url     : https://prove2.me/theorems/6e11ed01-822c-41c9-949a-26607c7290d7
-- title:
--   Finite-nine counting core aliases
-- statement:
--   Public names connecting the finite-nine endpoint geometry to the accepted counting definitions.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/tree/a46894f6078319d3001d06310531df50af0f6bbd/lean/Erdos9796Proof/P97

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna
-/

import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_MEC_Basic
import Definitions.Def_Erdos9796Counting_Moser_Triangle
import Definitions.Def_Erdos9796Counting_Moser_TriangleNonObtuse
import Definitions.Def_Erdos9796Counting_Cap_Structure
import Definitions.Def_Erdos9796Counting_Cap_PartitionFromMEC
import Definitions.Def_Erdos9796Counting_CircumscribedMECPacket

/-! Definition-only aliases required by the authenticated `Batch3N9` endpoint source. -/

open scoped EuclideanGeometry

namespace Batch3N9
namespace Problem97

export _root_.Problem97 (CapTriple CircumscribedMECPacket ConvexIndep MoserTriangle)

abbrev HasNEquidistantProperty := _root_.Erdos97.HasNEquidistantProperty

namespace MEC

export _root_.Problem97.MEC (mec NonObtuseCircumscribedMoserTriangle)

end MEC
end Problem97
end Batch3N9


