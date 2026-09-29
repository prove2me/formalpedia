-- Prove2me | Definitions.Def_AhlforsComplexAnalysis_Defs
-- name    : AhlforsComplexAnalysis_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T04:43:45.054537+00:00
-- url     : https://prove2.me/theorems/72ec6c5a-887a-4a0e-9916-18410665fd93
-- title:
--   Ahlfors: regions, simply connected regions (Def. 4.1), normal families (Def. 5.2)
-- statement:
--   This file fixes three notions from Ahlfors' *Complex Analysis* used throughout the series.
--
--   - **Region** (Ch. 3, §1.3, Definition 4): a set $\Omega\subseteq\mathbb C$ is a region if it is nonempty, open and connected. In Lean: `IsRegion Ω := IsOpen Ω ∧ IsConnected Ω` (Mathlib's `IsConnected` includes nonemptiness).
--   - **Simply connected region** (Ch. 4, §4.2, Definition 1): a region $\Omega$ is simply connected if its complement in the extended plane $\mathbb C\cup\{\infty\}$ is connected. In Lean the extended plane is the one-point compactification `OnePoint ℂ`, and the condition reads: the complement of the image of $\Omega$ in `OnePoint ℂ` is connected.
--   - **Normal family** (Ch. 5, §5.1, Definition 2, with values in $\mathbb C$): a family $\mathfrak F$ of functions is normal in $\Omega$ if every sequence $(F_n)$ of members of $\mathfrak F$ has a subsequence $(F_{\varphi(n)})$ and a limit function $g$ such that $F_{\varphi(n)}\to g$ uniformly on every compact subset $K\subseteq\Omega$. The limit need not belong to $\mathfrak F$.
-- source:
--   L. V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979 (ISBN 0-07-000657-1), Ch. 3 §1.3 Definition 4 (p. 57); Ch. 4 §4.2 Definition 1 (p. 139); Ch. 5 §5.1 Definition 2 (p. 220)

import Mathlib

namespace AhlforsComplexAnalysis

/-- Ahlfors, *Complex Analysis* (3rd ed.), Ch. 3, §1.3, Definition 4: a *region* is a nonempty,
open, connected subset of the (finite) complex plane. -/
def IsRegion (Ω : Set ℂ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω

/-- Ahlfors, Ch. 4, §4.2, Definition 1: a region is *simply connected* if its
complement with respect to the extended plane `ℂ ∪ {∞}` is connected. -/
def IsSimplyConnectedRegion (Ω : Set ℂ) : Prop :=
  IsRegion Ω ∧ IsConnected (((↑) : ℂ → OnePoint ℂ) '' Ω)ᶜ

/-- Ahlfors, Ch. 5, §5.1, Definition 2 (with values in `S = ℂ`): a family `𝔉` is
*normal in `Ω`* if every sequence of members of `𝔉` has a subsequence converging
uniformly on every compact subset of `Ω`. The limit need not lie in `𝔉`. -/
def IsNormalFamily (𝔉 : Set (ℂ → ℂ)) (Ω : Set ℂ) : Prop :=
  ∀ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ 𝔉) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ,
      ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn (fun n => F (φ n)) g Filter.atTop K

end AhlforsComplexAnalysis


