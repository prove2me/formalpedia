-- Prove2me | Definitions.Def_BlockSSM_Supplement_FTracker
-- name    : BlockSSM_Supplement_FTracker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:15.138766+00:00
-- url     : https://prove2.me/theorems/7c2f7466-3324-4ac2-8438-6d4c7398de7e
-- title:
--   Trackers over a field $F$ and $n_{b,F}(G)$
-- statement:
--   Let $F$ be a field. A **one-layer tracker over $F$** of a group $G$ with block bound $b$ is Definition 1 with every affine map taken over $F$: a block partition $n=n_1+\dots+n_m$ with $n_i\le b$, fixed across symbols; for each $g\in G$ a map $f_g(h)=A_gh+c_g$ with $A_g=\mathrm{diag}(A^{(1)}_g,\dots,A^{(m)}_g)$, $A^{(i)}_g\in F^{n_i\times n_i}$, $c_g\in F^n$; a start state $h_0\in F^n$; and an arbitrary decoder $F^n\to G$. Word maps, tracking ($\mathrm{dec}(F_s(h_0))=\pi(s)$ for every word) and finite-state ($\{F_s(h_0)\}$ finite) are as over $\mathbb C$, and $n_{b,F}(G)$ is the least hidden dimension of a finite-state tracker over $F$ that tracks $G$, or $\infty$.
--
--   This is the tracker side of Theorem 30.
--
--   **Formalization Note** A field-parametric copy of the complex tracker; infimum in $\mathbb N\cup\{\infty\}$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19), with Definition 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockSSM_wordProd

universe u v

namespace BlockSSM.Supplement

open BlockSSM

/-- The hidden state space `F^{n₁} × ⋯ × F^{n_m}` over a field `F`. -/
abbrev FState (F : Type v) {m : ℕ} (n : Fin m → ℕ) : Type v := ∀ i, Fin (n i) → F

/-- **One-layer tracker over a field `F`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19): Definition 1 (p.2)
with "all affine maps … taken over F": a block partition with `n_i ≤ b`, fixed across symbols; for
every `g ∈ G` block matrices `A_g^{(i)} ∈ F^{n_i×n_i}` and a bias `c_g ∈ Fⁿ`; a start state
`h₀ ∈ Fⁿ`; and an arbitrary decoder `Fⁿ → G`.

**Formalization Note.** The field-parametric copy of `BlockSSM.Tracker` (which is over `ℂ`);
`b : ℕ∞`, and blocks of size `0` or `m = 0` are allowed. -/
structure FTracker (F : Type v) [Field F] (G : Type u) (b : ℕ∞) where
  /-- The number of blocks. -/
  m : ℕ
  /-- The block sizes. -/
  n : Fin m → ℕ
  /-- Every block has size at most `b`. -/
  n_le : ∀ i, (n i : ℕ∞) ≤ b
  /-- The block matrices. -/
  A : G → ∀ i, Matrix (Fin (n i)) (Fin (n i)) F
  /-- The biases. -/
  c : G → FState F n
  /-- The start state. -/
  h₀ : FState F n
  /-- The decoder, an arbitrary function. -/
  dec : FState F n → G

namespace FTracker

variable {F : Type v} [Field F] {G : Type u} {b : ℕ∞}

/-- The transition `f_g(h) = A_g h + c_g`, block by block. -/
def step (T : FTracker F G b) (g : G) (h : FState F T.n) : FState F T.n :=
  fun i => (T.A g i).mulVec (h i) + T.c g i

/-- The word map `F_s = f_{g_T} ∘ ⋯ ∘ f_{g₁}` (first letter first). -/
def wordMap (T : FTracker F G b) (s : List G) (h : FState F T.n) : FState F T.n :=
  s.foldl (fun x g => T.step g x) h

/-- The hidden dimension `∑ n_i`. -/
def hiddenDim (T : FTracker F G b) : ℕ := ∑ i, T.n i

/-- The decoder tracks `G`: `dec(F_s(h₀)) = π(s)` for every word, the empty word included. -/
def Tracks [Group G] (T : FTracker F G b) : Prop :=
  ∀ s : List G, T.dec (T.wordMap s T.h₀) = wordProd s

/-- The tracker is finite-state: `R = {F_s(h₀)}` is finite. -/
def IsFiniteState (T : FTracker F G b) : Prop :=
  (Set.range fun s : List G => T.wordMap s T.h₀).Finite

end FTracker

/-- **`n_{b,F}(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19): the minimum hidden dimension of a
finite-state tracker over `F` whose decoder tracks `G`, or `∞`.

**Formalization Note.** Infimum in `ℕ∞`. -/
noncomputable def trackerDimF (F : Type v) [Field F] (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ T : FTracker F G b, T.Tracks ∧ T.IsFiniteState ∧ D = (T.hiddenDim : ℕ∞)}

end BlockSSM.Supplement


