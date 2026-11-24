-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_CheckpointTournaments
-- name    : Sensitivity214439_Phase0_Solutions_CheckpointTournaments
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:17.845878+00:00
-- url     : https://prove2.me/theorems/0132dd22-3ee6-4c5c-833d-32363f52896b
-- title:
--   Literal residue mask for the Paley tournament
-- statement:
--   The constant $\operatorname{paley2659Mask}$ is a natural-number bit mask encoding the selected nonzero quadratic-residue displacements modulo $2659$. Its bit at displacement $d$ is used to represent the circulant edge from $x$ to $x+d$. The exact integer is fixed in the formal definition; subsequent finite and algebraic lemmas establish its agreement with the square-displacement relation.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/CheckpointTournaments.lean lines 102–102; SHA256 5c72e65c1dabf4353618467cf5ac22eb0706243af7d3fd193511a9de00120ea1; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal.TournamentHighRows
end Sensitivity213981Formal.TournamentHighRows
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Full tournament laws for the actual graphs, including the typed API. -/

namespace SensitivityRankedConstruction

open Sensitivity213981Formal.TournamentHighRows
open SensitivityHighHeadGuardBridge









end SensitivityRankedConstruction

namespace SensitivityRankMapCheckpoint

open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open Sensitivity213981Formal.TournamentHighRows

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000







def paley2659Mask : ℕ := 104458797852377733311337320016439584192658951451981616700425383257065881288800879866031454219327325418921204832113154360702895650291850064707560452746565312570756576520876622750252569952563358740781376214489061673934501750142307807223842359774433078844241216867633646168286364882563329846174035380385703966442917741852519139122850244147356871884495157532470394484244455767175542479414517022562395072745810859845636247089341724817642421383575861024177369825615829551084487853146852798640604417652720132985027406916676620402366642872736964249729175431124926859857851854005723735891094767332747885190495203696578106021187302435830903328689932451572178528361814392599648561864736988144577752745440777903874817163932472978952774760617274673047786064501934913060491704374931368139771094007701280420940810994



















end SensitivityRankMapCheckpoint


