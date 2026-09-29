-- Prove2me | Definitions.Def_P2M_Derive_AutomorphicForm_ArchDirComplex_DecidableEq
-- name    : P2M_Derive_AutomorphicForm_ArchDirComplex_DecidableEq
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/d910ff22-6de1-5871-b560-f543ae4c79c9
-- title:
--   Derived instance: AutomorphicForm_ArchDirComplex_DecidableEq
-- statement:
--   A `deriving instance` companion module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Derive/D_AutomorphicForm_ArchDirComplex_DecidableEq.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

deriving instance DecidableEq for AutomorphicForm.ArchDirComplex


