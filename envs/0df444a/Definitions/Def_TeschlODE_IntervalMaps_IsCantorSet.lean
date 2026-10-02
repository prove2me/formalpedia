-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_IsCantorSet
-- name    : TeschlODE_IntervalMaps_IsCantorSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:18:24.673009+00:00
-- url     : https://prove2.me/theorems/e2c0891f-11d9-4bf2-acf8-c4b971e19e3b
-- title:
--   Cantor set: compact, totally disconnected and perfect
-- statement:
--   A subset $C$ of a topological space is a **Cantor set** if it is compact, totally disconnected and perfect, i.e. every point of $C$ is an accumulation point of $C$.
--
--   **Formalization Note.** "Totally disconnected" is Mathlib's `IsTotallyDisconnected` (every preconnected subset is a subsingleton). For subsets of $\mathbb{R}$ this is the book's §11.4 reading "contains no open subintervals" (p. 299), and it agrees with §11.5's separation definition (p. 302; Problem 11.8). "Perfect" is Mathlib's `Preperfect` (every point is an accumulation point); closedness is already implied by compactness in a Hausdorff space.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 299, §11.4 (definition of Cantor set); p. 302, §11.5

import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.4, p. 299 (and §11.5, p. 302): a Cantor set is a compact set which is totally
disconnected and perfect (every point of it is an accumulation point of it). Total
disconnectedness is Mathlib's `IsTotallyDisconnected` (every preconnected subset is a
subsingleton); for subsets of `ℝ` this is the book's "contains no open subintervals"
(Problem 11.8). -/
def IsCantorSet {X : Type*} [TopologicalSpace X] (C : Set X) : Prop :=
  IsCompact C ∧ IsTotallyDisconnected C ∧ Preperfect C

end TeschlODE.IntervalMaps


