-- Prove2me | Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
-- name    : Zeta23_FromPNTPlus_StrongPNTPrefix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:04:53.042281+00:00
-- url     : https://prove2.me/theorems/b2eddeb8-7c2f-4952-854c-4fc7e202b2ea
-- title:
--   Blaschke-factor machinery for counting zeros in a disk
-- statement:
--   This bundle (the sorry-free prefix of the PrimeNumberTheoremAnd file `StrongPNT.lean`, truncated after the Blaschke-factor / Borel–Carathéodory bound on zeros in a disk) defines the machinery for factoring an analytic function through its zeros in a disk.
--
--   **`SetOfZeros`** $R\,f := \{\rho \in \mathbb{C} : \|\rho\| \le R,\ f(\rho) = 0\}$, the zeros of $f$ in the closed disk of radius $R$; the lemma `finiteSetOfZeros_mono` shows finiteness passes down from radius $1$ to any $r < 1$. **`ZeroFactor`** $f\,z$ is the analytic cofactor of $f$ at $z$: when $f$ is analytic at $z$ with finite vanishing order, the function $g$ with $f(s) = (s - z)^{\mathrm{ord}}g(s)$ and $g(z) \neq 0$ (junk value $0$ otherwise). **`Cf`** $r\,f\,z$ divides $f$ (or its zero factor, at a zero) by $\prod_\rho (z - \rho)^{\mathrm{ord}_\rho f}$ over the zeros in radius $r$ — the function with the zeros in the disk of radius $r$ removed. **`BlaschkeB`** $r\,R\,f\,z := C_f(z)\prod_\rho (R - z\bar\rho/R)^{\mathrm{ord}_\rho f}$, the Blaschke-type product renormalisation whose modulus on $|z| = R$ matches $|f|$ up to controlled factors; each definition returns a junk value ($1$) when the zero set is infinite, so no finiteness hypothesis is carried in the types.
--
--   The surrounding module proves the classical Borel–Carathéodory-style bound `ZerosBound` on the number of zeros in a disk. In the project this contour-free zero-counting machinery supports the unconditional inputs (the local zero count $N(t+1) - N(t) \ll \log(t+3)$ of H-RvM) consumed by the tail estimates of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal

/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory








def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ := {ρ : ℂ | ‖ρ‖ ≤ R ∧ f ρ = 0}

lemma finiteSetOfZeros_mono {r : ℝ} {f : ℂ → ℂ}
    (r_lt_one : r < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) :
    (SetOfZeros r f).Finite := by
  apply Set.Finite.subset finiteZeros
  unfold SetOfZeros
  refine setOf_subset_setOf.mpr ?_
  intro z hz
  exact ⟨by linarith, hz.2⟩

open Classical
noncomputable def ZeroFactor (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h1 : AnalyticAt ℂ f z then
    if h2 : analyticOrderAt f z ≠ ⊤ then
      (h1.analyticOrderAt_ne_top.mp h2).choose z
    else 0
  else 0


noncomputable def Cf (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      ZeroFactor f z / ∏ ρ ∈ (finite_zeros_mono.toFinset \ {z}), (z - ρ) ^ (analyticOrderNatAt f ρ)
    else
      f z / ∏ ρ ∈ (finite_zeros_mono.toFinset), (z - ρ) ^ (analyticOrderNatAt f ρ)
  else 1



noncomputable def BlaschkeB (r R : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if finite_zeros_mono : (SetOfZeros r f).Finite then
    (Cf r f) z * (∏ ρ ∈ finite_zeros_mono.toFinset, (R - z * (conj ρ) / R) ^ (analyticOrderNatAt f ρ))
  else 1


