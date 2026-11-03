-- Prove2me | Definitions.Def_levy_foundations_isCadlag
-- name    : levy_foundations_isCadlag
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:31:05.663148+00:00
-- url     : https://prove2.me/theorems/ed06a179-7c79-4add-9824-d1add8bb190e
-- title:
--   Càdlàg functions on preordered topological domains
-- statement:
--   For any preordered topological domain α and topological codomain β, a function f : α → β is càdlàg when at each index it is continuous from the right, relative to indices at least that index, and has a limit approached through strictly smaller indices. Real-valued paths indexed by nonnegative time are a special case.
-- source:
--   Adapted from Shmuel Link, LeanLevy (MIT), frozen commit 7e73fd9b23ad52956ec2756a815889a783131ce4, https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/Cadlag.lean#L44-L49. Generic preordered topological-domain definition; independently authored Prove2Me draft awaiting remote Lean compilation.

import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

open Filter Set Topology
open scoped NNReal
namespace LevyFoundations
def isCadlagAt {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
    (f : α → β) (t : α) : Prop :=
  ContinuousWithinAt f (Ici t) t ∧
    ∃ l : β, Tendsto f (𝓝[Iio t] t) (𝓝 l)
def isCadlag {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
    (f : α → β) : Prop :=
  ∀ t, isCadlagAt f t
end LevyFoundations


