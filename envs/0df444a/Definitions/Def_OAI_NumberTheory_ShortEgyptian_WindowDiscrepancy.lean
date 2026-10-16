-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
-- name    : OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:23:39.588308+00:00
-- url     : https://prove2.me/theorems/121210ff-aba8-4981-a344-5262caac320e
-- title:
--   The window of residues with representative below $\delta q$
-- statement:
--   Let $q$ be a natural number and $\delta$ a real number, and write $W_q(L)=\{n\bmod q:\ 0\le n<L\}\subseteq\mathbb{Z}/q\mathbb{Z}$ for the initial window of length $L\in\mathbb{N}$. The file defines the residue window
--
--   $$R_q(\delta)=W_q\bigl(\lceil\delta q\rceil\bigr)=\{\,n\bmod q:\ 0\le n<\lceil\delta q\rceil\,\},$$
--
--   where $\lceil\cdot\rceil$ is the ceiling rounded to a natural number; it is $0$ for non-positive arguments, so $R_q(\delta)$ is empty when $\delta q\le 0$. For $q\ge 1$ and $\delta\le 1$, a residue $x$ belongs to $R_q(\delta)$ if and only if its least nonnegative representative $\bar x\in\{0,\dots,q-1\}$ satisfies $\bar x<\delta q$.
--
--   This is the set of small residues in the discrepancy step. In the surrounding development it is shown that if $\mu\ge 0$ is a probability distribution on $\mathbb{Z}/q\mathbb{Z}$ with $q\ge 1$, $0<\delta\le 1/256$, $H\ge 1$ with $2H\delta^4\ge 1$, and $|\widehat\mu(k)|\le\delta^3$ for every nonzero frequency $k$ whose circular distance $\min(\bar k,q-\bar k)$ from $0$ is at most $H$, then $\mu(R_q(\delta))\ge\delta/2$; here $\widehat\mu(k)=\sum_x\mu(x)\exp(-2\pi i k\bar x/q)$. For the greedy step applied to a fraction $u/N$, the residue $u\lceil N/u\rceil-N$ is the least nonnegative representative of $-N$ modulo $u$, so landing in $R_u(\delta)$ means that the step leaves a remainder numerator smaller than $\delta u$.
--
--   **Formalization Note** The Lean name is `residueWindow`, defined through `natWindow` and the natural ceiling `Nat.ceil`; membership is characterized by the separate lemma `mem_residueWindow`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/WindowDiscrepancy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def residueWindow (q : ℕ) (δ : ℝ) : Finset (ZMod q) :=
  natWindow q ⌈δ * q⌉₊

end ShortEgyptian

end OAI


