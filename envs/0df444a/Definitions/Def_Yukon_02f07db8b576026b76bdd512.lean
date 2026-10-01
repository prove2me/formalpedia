-- Prove2me | Definitions.Def_Yukon_02f07db8b576026b76bdd512
-- name    : Yukon_02f07db8b576026b76bdd512
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:47:12.488836+00:00
-- url     : https://prove2.me/theorems/bed55f7b-aff6-4287-889d-a4b67c9fb33b
-- title:
--   YukonModule.VCVio.Prelude.part0
-- statement:
--   Source module VCVio.Prelude.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/Prelude.lean
--
--   yukon-proof-operation:08c80933653a95dae93b37e379d01f0d8c8d12e1453745953a45c96d1b05c549
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MDhjODA5MzM2NTNhOTVkYWU5M2IzN2UzNzlkMDFmMGQ4YzhkMTJlMTQ1Mzc0NTk1M2E0NWM5NmQxYjA1YzU0OSIsImhhc2giOiI4N2M3MzBjNzM1NjIxYzhhMTc1ODRmZjNlOTVmYjVkOWNlZGJiYTEwMmYxOGQ5MjgxMjI4MGY3MTNlZTJhYWRmIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl8wMmYwN2RiOGI1NzYwMjZiNzZiZGQ1MTIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2025 Devon Tuma, Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Definitions.Def_Yukon_ec6e56db18cc5472c07c58c9



public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Vector.Defs
public import Mathlib.Data.Finset.Card
public import Init
meta import Definitions.Def_Yukon_ec6e56db18cc5472c07c58c9
set_option backward.isDefEq.respectTransparency.types false
/-!
# VCVio Prelude

Shared project-wide declarations and simp attributes imported throughout `VCVio`.
-/

@[expose] public section

declare_aesop_rule_sets [UnfoldEvalDist]

/-- Simp set for game-hopping proofs: evalDist, probOutput, simulateQ, wp, relTriple rules. -/
register_simp_attr game_rule

/-- VCVio-specific extension of PolyFun's `handler_nf` normalization set. -/
register_simp_attr handler_simp


