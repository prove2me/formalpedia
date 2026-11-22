-- Prove2me | Definitions.Def_Arm64_Spec_RustRuntime
-- name    : Arm64_Spec_RustRuntime
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T00:14:25.030167+00:00
-- url     : https://prove2.me/theorems/39dc566b-22b2-4f27-b97f-ff0322f97f28
-- title:
--   Arm64.Trusted.Spec.RustRuntime — Rust Runtime Panic Hooks
-- statement:
--   Part of DeepMind's Lean model of AArch64 Linux user processes, `Arm64.Trusted` (google-deepmind/code-verification, Apache License 2.0): the module [Arm64/Trusted/Spec/RustRuntime.lean](https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustRuntime.lean), published as a definitions bundle with its Lean namespace (`Arm64`) and names unchanged. It differs from upstream only as the "MODIFIED for prove2.me" notice after its license header states. After elaboration, every constant of the 56 republished bundles was compared with upstream's and all 5,962 were identical ([compare_consts.py](https://github.com/dbenbenn/arm64-semantics-p2m/blob/675d823511a48f6e2d2d8e0c47aca8eff28dbe2b/tools/compare_consts.py)). The module docstring is upstream's.
-- source:
--   Google DeepMind, code-verification (Arm64.Trusted), Apache License 2.0, commit 8c8d371f1962ac73435c8eb148678991f5c3470d, module Arm64/Trusted/Spec/RustRuntime.lean, https://github.com/google-deepmind/code-verification/blob/8c8d371f1962ac73435c8eb148678991f5c3470d/arm64-semantics/Arm64/Trusted/Spec/RustRuntime.lean

/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

/-
MODIFIED for prove2.me (republication of DeepMind's `Arm64.Trusted`, upstream
google-deepmind/code-verification commit 8c8d371f, file `Arm64/Trusted/Spec/RustRuntime.lean`):
every import of `Arm64.Trusted.<M>` renamed to the bundle `Definitions.Def_Arm64_<M>`.
No other change.
-/

module

public import Definitions.Def_Arm64_ISA_Semantics

/-!
# Rust Runtime Panic Hooks

Models Rust `panic = abort` entry points by wrapping a `Program` hook table (`Rust.withPanics`)
so calls to `core::panicking::*`, `unwrap`/`expect` failure paths, slice bounds checks, and
allocation error handlers transition `s.status` to `.Panicked`.
-/

@[expose] public section

namespace Arm64.Rust

/-- Demangled names of functions that start a panic. Everything in `core::panicking` panics;
    the others are the out-of-line panic paths of `unwrap`/`expect`, slice indexing, and
    allocation failure. -/
def isPanicSymbol (name : String) : Bool :=
  name.startsWith "core::panicking::" ||
  [ "core::result::unwrap_failed",
    "core::option::unwrap_failed",
    "core::option::expect_failed",
    "core::slice::index::slice_start_index_len_fail",
    "core::slice::index::slice_end_index_len_fail",
    "core::slice::index::slice_index_order_fail",
    "core::slice::index::slice_index_fail",
    "alloc::raw_vec::handle_error",
    "alloc::raw_vec::capacity_overflow",
    "alloc::alloc::handle_alloc_error" ].contains name

/-- The effect of entering a panic. -/
def panicked (s : State) : State :=
  { s with status := .Panicked }

/-- `hooks`, with every panic function (`isPanicSymbol`) mapped to `panicked`. -/
def withPanics (hooks : String → Option (State → State) := fun _ => none) :
    String → Option (State → State) :=
  fun name => if isPanicSymbol name then some panicked else hooks name

end Arm64.Rust


