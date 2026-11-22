-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_WeakConvergence
-- name    : LeanPool_NemytskiiLebesgue_WeakConvergence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:34:47.950235+00:00
-- url     : https://prove2.me/theorems/b748206e-5310-4dde-906e-2a5494786e81
-- title:
--   Weak Convergence
-- statement:
--   Definitions and structural lemmas for Weak Convergence, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/WeakConvergence.lean

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
@[expose] def _root_.Function.NemytskiiWeaklyConvergesTo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ → E) (v : E) :
    Prop :=
  ∀ f : E →L[ℝ] ℝ, Tendsto (fun n : ℕ => f (u n)) atTop (𝓝 (f v))
end NemytskiiLebesgue


