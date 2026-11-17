-- Prove2me | Definitions.Def_DSICHardRev_Supplement_Domains
-- name    : DSICHardRev_Supplement_Domains
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:09:08.69423+00:00
-- url     : https://prove2.me/theorems/019859f6-e78b-4f46-9f19-1e00d06ae5df
-- title:
--   Valuation domains for Theorems 1.2 and 1.4–1.7: XOS, submodular, weighted matroid rank and matroid rank
-- statement:
--   Let $M=[m]$ be the set of items and let a valuation be a function $v:2^{M}\to\mathbb R$. Write $R=\{2^{s/2}t/m : s\in[-2^m,2^m]\cap\mathbb Z,\ t\in[0,m^5]\cap\mathbb Z\}$ for the value range of the paper (p.8).
--
--   1. **Submodularity** (Definition 2.18). A valuation $v$ is submodular if for every item $j$ the marginal value $v(S\cup\{j\})-v(S)$ is monotone non-increasing in $S$: for all $S\subseteq T$,
--   $$
--   v(T\cup\{j\})-v(T)\;\le\;v(S\cup\{j\})-v(S).
--   $$
--   2. $\mathcal D_{\mathrm{XOS}}(m)$: monotone XOS valuations (maxima of finitely many, at least one, non-negative additive functions, Definition 2.19) with every value in $R$.
--   3. $\mathcal D_{\mathrm{SUB}}(m)$: monotone submodular valuations with every value in $R$.
--   4. $\mathcal D_{\mathrm{WMR}}(m)$: weighted matroid rank valuations $v(S)=\max_{T\in\mathcal M}w(S\cap T)$ (Definition 2.15) with every value in $R$.
--   5. $\mathcal D_{\mathrm{MR}}(m)$: matroid rank functions $r(S)=\max_{T\in\mathcal M}|S\cap T|$ (Definition 2.14).
--
--   These are the valuation classes of Theorems 1.2 (XOS), 1.4 and 1.6 (matroid rank), 1.5 (weighted matroid rank) and 1.7 (submodular).
--
--   **Formalization Note** Items are `Fin m`. The XOS, weighted matroid rank and matroid rank predicates and the range $R$ are the base mission's published definitions. Matroid rank values are integers in $[0,m]$, which lie in $R$ for $m\ge1$, so no range condition is written for $\mathcal D_{\mathrm{MR}}$. $v(\emptyset)=0$ is not required, as in the paper.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.1 p.8 (range R), §2.3 pp.9–10: monotone valuations, Definitions 2.14, 2.15, 2.18, 2.19

import Mathlib
import Definitions.Def_DSICHardRev_GSDomain
import Definitions.Def_DSICHardRev_ValuationClasses

namespace DSICHardRev

namespace Supplement

/-!
# Valuation domains of Theorems 1.2 and 1.4–1.7

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…): the range `R`, §2.1, p.8; monotone valuations, §2.3,
p.9; Definitions 2.13–2.15, 2.18 and 2.19, p.10.

**Formalization Note.**
* Items are `Fin m` (all `m` items), valuations are real functions on `Finset (Fin m)`.
* `DXOS m` (Theorem 1.2): monotone XOS valuations (the published `IsXOS`: a maximum of finitely
  many, at least one, non-negative additive functions) with every value in the published range
  `Rset m` of p.8. It mirrors the published `DGS m`.
* `IsSubmodular v` is Definition 2.18 verbatim: for every item `j` the marginal value
  `v(S ∪ {j}) − v(S)` is non-increasing in `S` (for all `S ⊆ T`, including `j ∈ T`).
* `DSUB m` (Theorem 1.7): monotone submodular valuations with every value in `Rset m`.
* `DWMR m` (Theorem 1.5): weighted matroid rank valuations (the published
  `IsWeightedMatroidRank`, Definition 2.15; monotone and non-negative automatically) with every
  value in `Rset m`.
* `DMR m` (Theorems 1.4, 1.6): matroid rank functions (the published `IsMatroidRankFn`,
  Definition 2.14, a Mathlib `Matroid (Fin m)` with ground set `univ`). Their values are integers in
  `[0, m]`, which lie in `Rset m` for `m ≥ 1`, so the range adds nothing and is not written.
* `v ∅ = 0` is not required, as the paper does not require it.
-/

/-- The XOS domain of Theorem 1.2: monotone XOS valuations on `Fin m` with every value in
`Rset m`. -/
def DXOS (m : ℕ) : Set (Finset (Fin m) → ℝ) :=
  {v | Monotone v ∧ (∀ S, v S ∈ Rset m) ∧ IsXOS v}

/-- Submodularity (Definition 2.18): for every item `j`, the marginal value
`v(S ∪ {j}) − v(S)` is monotone non-increasing in `S`. -/
def IsSubmodular {ι : Type} [DecidableEq ι] (v : Finset ι → ℝ) : Prop :=
  ∀ j : ι, ∀ S T : Finset ι, S ⊆ T → v (insert j T) - v T ≤ v (insert j S) - v S

/-- The submodular domain of Theorem 1.7: monotone submodular valuations on `Fin m` with every
value in `Rset m`. -/
def DSUB (m : ℕ) : Set (Finset (Fin m) → ℝ) :=
  {v | Monotone v ∧ (∀ S, v S ∈ Rset m) ∧ IsSubmodular v}

/-- The weighted matroid rank domain of Theorem 1.5: weighted matroid rank valuations on `Fin m`
with every value in `Rset m`. -/
def DWMR (m : ℕ) : Set (Finset (Fin m) → ℝ) :=
  {v | IsWeightedMatroidRank v ∧ ∀ S, v S ∈ Rset m}

/-- The matroid rank domain of Theorems 1.4 and 1.6: rank functions of matroids on `Fin m`. -/
def DMR (m : ℕ) : Set (Finset (Fin m) → ℝ) :=
  {r | IsMatroidRankFn r}

end Supplement

end DSICHardRev


