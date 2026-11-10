-- Prove2me | Definitions.Def_WeightedSetCoverWorstCase_Dynamic_HPC
-- name    : WeightedSetCoverWorstCase_Dynamic_HPC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:29:14.113854+00:00
-- url     : https://prove2.me/theorems/a5d435ef-b3d3-4c81-a326-e42a919fc34c
-- title:
--   Hierarchical partial coverings and Invariant 6.1
-- statement:
--   A **hierarchical partial covering** (`HPC inst V`) has a finite universe $U$ of element versions of type $V$ (each with a base element; a set $s$ contains a version iff it contains its base), its alive part ($\mathrm{Dead}=U\setminus\mathrm{Alive}$), levels $\ell(e)$, passive levels $\wp\ell(e)$ and a multiset $C$ of set copies with coverages and levels. `IsHPC L` requires $\mathrm{Alive}\subseteq U$, $\ell(e)\in[0,L]$, $\wp\ell(e)\in[0,L+1]$ and $\mathrm{cov}(s)\subseteq s\cap U$; the copies need not cover $U$.
--
--   $\mathrm{Act}_{\le k}=\{e:\ell(e)\le k<\wp\ell(e)\}$, $\mathrm{Act}_{=k}=\{e:\ell(e)=k<\wp\ell(e)\}$, $\mathrm{Pass}_{\le k}=U_{\le k}\setminus\mathrm{Act}_{\le k}$.
--
--   Invariant 6.1, for a cost function $c$: (1) **level consistency** $\wp\ell(e)\ge\ell(e)$, with equality for dead $e$; (2) **weak $\varepsilon$-stability** at $k$: $|\mathrm{Act}_{=k}\cap s|<(1+\varepsilon)^{k+1}c_s$ for all input sets $s$ (strong: with $\mathrm{Act}_{\le k}$), at all $k\in[0,L]$; (3) **$\delta$-tidiness** $|\mathrm{Pass}_{\le k}|\le\delta|\mathrm{Act}_{\le k}|$ at all $k\in[0,L]$; (4) **coverage size**: $\ell(s)\le\lfloor\log_{1+\varepsilon}(|\mathrm{cov}(s)|/c_s)\rfloor$, every $e\in\mathrm{cov}(s)$ has $\ell(e)\le\ell(s)$, and coverages of different copies are disjoint. `Inv61Weak` bundles (1)–(4) with weak stability.
--
--   **Formalization Note.** (4) is written $(1+\varepsilon)^{\ell(s)}c_s\le|\mathrm{cov}(s)|$: equivalent for nonempty coverage, and false for empty coverage, where the paper's logarithm is $-\infty$ (Lean's `log 0 = 0` is never used).
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, §6.2, p. 22 (PDF 25); §6.1 footnote 6, p. 21 (PDF 24)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem

namespace WeightedSetCoverWorstCase.Dynamic

/-!
# Hierarchical partial coverings and Invariant 6.1

Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), §6.2, p. 22 (PDF 25).

Elements are *versions* of type `V`; each version has a base element `base e ∈ Fin u`, and a set
`s` contains `e` iff it contains `base e` (§6.1: a reinsertion is a brand-new version; footnote 6).
With `V = Fin u` and `base = id` this is the paper's plain universe.

A hierarchical partial covering `(U, ℓ, ℘ℓ, C, cov)` has a finite universe `U` of versions (with its
alive part; `Dead = U ∖ Alive`), integer levels `ℓ(e) ∈ [0, L]`, passive levels `℘ℓ(e) ∈ [0, L+1]`,
and a multiset `C` of set copies, each with a coverage `cov(s) ⊆ s ∩ U` and a level `ℓ(s)`.
The sets of `C` need not cover `U`.

**Formalization Note.** The coverage-size condition `ℓ(s) ≤ ⌊log_{1+ε}(|cov(s)|/c_s)⌋` is written
`(1+ε)^{ℓ(s)} c_s ≤ |cov(s)|`, which is equivalent for nonempty coverage and false for empty
coverage (where the logarithm is `-∞`); it avoids Lean's `log 0 = 0`.
Stability is parametrised by the cost function `c` it uses (the source's costs; the algorithm uses
its normalised costs `ncost`).
-/

/-- A hierarchical partial covering over the instance `inst`, with versions of type `V`. -/
structure HPC (inst : Instance) (V : Type) where
  /-- the base element of each version -/
  base : V → Fin inst.u
  /-- the universe `U` -/
  U : Finset V
  /-- the alive elements (`Dead = U ∖ alive`) -/
  alive : Finset V
  /-- the level `ℓ(e)` -/
  lvl : V → ℕ
  /-- the passive level `℘ℓ(e)` -/
  plvl : V → ℕ
  /-- the multiset `C` of set copies with their coverages and levels -/
  C : List (Copy inst.m V)

namespace HPC

variable {inst : Instance} {V : Type} [DecidableEq V] (H : HPC inst V)

/-- The version `e` belongs to the input set `s`. -/
def InSet (s : Fin inst.m) (e : V) : Prop := H.base e ∈ inst.S s

instance (s : Fin inst.m) (e : V) : Decidable (H.InSet s e) := by unfold InSet; infer_instance

/-- `X ∩ s`. -/
def inter (X : Finset V) (s : Fin inst.m) : Finset V := X.filter (H.InSet s)

/-- `U_{≤k}`. -/
def Ule (k : ℕ) : Finset V := H.U.filter fun e => H.lvl e ≤ k

/-- `Act_{≤k} = {e : ℓ(e) ≤ k < ℘ℓ(e)}`. -/
def Actle (k : ℕ) : Finset V := H.U.filter fun e => H.lvl e ≤ k ∧ k < H.plvl e

/-- `Act_{=k} = {e : ℓ(e) = k < ℘ℓ(e)}`. -/
def Acteq (k : ℕ) : Finset V := H.U.filter fun e => H.lvl e = k ∧ k < H.plvl e

/-- `Pass_{≤k} = U_{≤k} ∖ Act_{≤k}`. -/
def Passle (k : ℕ) : Finset V := H.Ule k \ H.Actle k

/-- The data form a hierarchical partial covering with level bound `L`: `Alive ⊆ U`, levels in
`[0, L]`, passive levels in `[0, L+1]`, and every coverage inside `s ∩ U`. -/
def IsHPC (L : ℕ) : Prop :=
  H.alive ⊆ H.U ∧ (∀ e ∈ H.U, H.lvl e ≤ L ∧ H.plvl e ≤ L + 1) ∧
    ∀ c ∈ H.C, c.cov ⊆ H.inter H.U c.set

/-- Invariant 6.1 (1), level consistency: `℘ℓ(e) ≥ ℓ(e)`, with equality for dead elements. -/
def LevelConsistent : Prop :=
  ∀ e ∈ H.U, H.lvl e ≤ H.plvl e ∧ (e ∉ H.alive → H.plvl e = H.lvl e)

/-- Invariant 6.1 (2): weakly `ε`-stable at level `k` (w.r.t. the costs `c`):
`|Act_{=k} ∩ s| < (1+ε)^{k+1} c_s` for every input set `s`. -/
def WeaklyStableAt (c : Fin inst.m → ℝ) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ s : Fin inst.m, ((H.inter (H.Acteq k) s).card : ℝ) < (1 + ε) ^ (k + 1) * c s

/-- Invariant 6.1 (2): strongly `ε`-stable at level `k`: `|Act_{≤k} ∩ s| < (1+ε)^{k+1} c_s`. -/
def StronglyStableAt (c : Fin inst.m → ℝ) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ s : Fin inst.m, ((H.inter (H.Actle k) s).card : ℝ) < (1 + ε) ^ (k + 1) * c s

/-- Weakly `ε`-stable at all levels `k ∈ [0, L]`. -/
def WeaklyStable (c : Fin inst.m → ℝ) (ε : ℝ) (L : ℕ) : Prop :=
  ∀ k ≤ L, H.WeaklyStableAt c ε k

/-- Strongly `ε`-stable at all levels `k ∈ [0, L]`. -/
def StronglyStable (c : Fin inst.m → ℝ) (ε : ℝ) (L : ℕ) : Prop :=
  ∀ k ≤ L, H.StronglyStableAt c ε k

/-- Invariant 6.1 (3): `δ`-tidy at level `k`: `|Pass_{≤k}| ≤ δ |Act_{≤k}|`. -/
def TidyAt (δ : ℝ) (k : ℕ) : Prop := ((H.Passle k).card : ℝ) ≤ δ * (H.Actle k).card

/-- `δ`-tidy at all levels `k ∈ [0, L]`. -/
def Tidy (δ : ℝ) (L : ℕ) : Prop := ∀ k ≤ L, H.TidyAt δ k

/-- Invariant 6.1 (4), coverage size: `ℓ(s) ≤ ⌊log_{1+ε}(|cov(s)|/c_s)⌋` (as
`(1+ε)^{ℓ(s)} c_s ≤ |cov(s)|`), every `e ∈ cov(s)` has `ℓ(e) ≤ ℓ(s)`, and the coverages of
different copies are mutually disjoint. -/
def CoverageSize (c : Fin inst.m → ℝ) (ε : ℝ) : Prop :=
  (∀ cp ∈ H.C, (1 + ε) ^ cp.lvl * c cp.set ≤ (cp.cov.card : ℝ) ∧ ∀ e ∈ cp.cov, H.lvl e ≤ cp.lvl) ∧
    H.C.Pairwise fun a b => Disjoint a.cov b.cov

/-- Invariant 6.1 with **weak** stability (strong stability implies it). -/
def Inv61Weak (c : Fin inst.m → ℝ) (L : ℕ) (ε δ : ℝ) : Prop :=
  H.LevelConsistent ∧ H.WeaklyStable c ε L ∧ H.Tidy δ L ∧ H.CoverageSize c ε

/-- The base elements of the alive versions. -/
def aliveBase : Finset (Fin inst.u) := H.alive.image H.base

end HPC

end WeightedSetCoverWorstCase.Dynamic


