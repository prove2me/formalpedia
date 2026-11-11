-- Prove2me | Definitions.Def_MarginMaxima_Critical_BlockSystem
-- name    : MarginMaxima_Critical_BlockSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:01:48.902229+00:00
-- url     : https://prove2.me/theorems/b5fd837f-08da-41b1-94b7-7fe4c1886f49
-- title:
--   Block systems with parameters $(g,s,\kappa)$ (Definition 4.1), $(M,j)$-regularity, realization by $r$ heads, and the random sampling of §4
-- statement:
--   Fix a unit vector $h_0$. Let $g>0$, $s\ge0$, $0\le\kappa<1$ with $\kappa^2+s\ge g$, and $\alpha^2=1-\kappa^2$. A **block system** with parameters $(g,s,\kappa)$ on a finite set $C$ consists of a Hilbert space $\mathcal L\perp h_0$, vectors $\xi_y\in\mathcal L$ with $\|\xi_y\|=\alpha$ ($y\in C$), and a family of subsets of $C$, the **blocks**, with vectors $\ell_B\in\mathcal L$, $\|\ell_B\|\le\alpha$. The documents $v_y=\xi_y+\kappa h_0$ and heads $u_B=\ell_B-\kappa h_0$ satisfy
--   $$\langle u_B,v_y\rangle\ge s+g\ (y\in B),\qquad \langle u_B,v_y\rangle\le s-g\ (y\notin B).$$
--   It is **$(M,j)$-regular** if the blocks form $j$ classes, each a partition of $C$ into sets of size $M$, and blocks of different classes share at most one point. The **null head** is $-\kappa h_0$. A set $Y\subseteq C$ is **realized by $r$ heads** if for every $\sigma\in\{\pm1\}^Y$ there are $\ell_1,\dots,\ell_r\in\mathcal L$ of norm at most $\alpha$ with $\max_i\langle\ell_i-\kappa h_0,v_y\rangle\ge s+g$ if $\sigma_y=+1$ and $\le s-g$ if $\sigma_y=-1$.
--
--   **Random sampling.** Let $M_0\le M$ be an integer, $p=M_0/M$ and $\pi_0=\Pr[\mathrm{Bin}(M-1,p)=M_0-1]$. $X\subseteq C$ contains each point independently with probability $p$, and $S\subseteq C$ each point independently with probability $\delta$, independently of $X$. A block $B$ is **chosen** if $|B\cap X|=M_0$ and $B\cap X\subseteq S$; $H$ is the number of chosen blocks and $U$ the set of points of $X\cap S$ in no chosen block.
--
--   These objects carry the probabilistic argument (Lemmas 4.2–4.4) shared by the paper's constructions.
--
--   **Formalization Note.** The Hilbert space $\mathcal L$ is a type `L` (complete real inner product space), and $h_0$ is kept implicit: since $\ell,\xi\perp h_0$ and $\|h_0\|=1$, $\langle\ell-\kappa h_0,\xi+\kappa h_0\rangle=\langle\ell,\xi\rangle-\kappa^2$, which is `BlockSystem.score`; the null head is $\ell=0$. Blocks are indexed by a type `β` (`blk b : Finset C`, `ℓ b : L`); `ValidParams g s κ` is a field. `IsRegular M j` asks for a class map `cls : β → Fin j` with every block of size `M`, every point in exactly one block of each class, and blocks of different classes meeting in at most one point. `RealizesWith S Y r P` asks, for every labelling `σ : C → Bool` (only its values on `Y` matter), for `ℓs : Fin r → L` of norm at most $\alpha$, each satisfying `P`, with some head scoring at least $s+g$ on each positive $y\in Y$ and all heads at most $s-g$ on each negative one (the max over $r\ge1$ heads written as ∃/∀); `Realizes` is `P = True` and `BlockOrNull ℓ` is `ℓ = 0 ∨ ∃ b, ℓ = S.ℓ b`. `sampleProb p δ E` is $\sum_{X,S}p^{|X|}(1-p)^{|C|-|X|}\delta^{|S|}(1-\delta)^{|C|-|S|}\,1[E(X,S)]$; `numChosen`, `uncovered` are $H$ and $U$; `pi0 M M0 p` is $\binom{M-1}{M_0-1}p^{M_0-1}(1-p)^{M-M_0}$.
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 8, Definition 4.1, the paragraph after it, and the sampling paragraph before Lemma 4.2

import Mathlib

namespace MarginMaxima.Critical

/-- The parameter conditions of Definition 4.1: `g > 0`, `s ≥ 0`, `0 ≤ κ < 1`, `κ² + s ≥ g`. -/
def ValidParams (g s κ : ℝ) : Prop :=
  0 < g ∧ 0 ≤ s ∧ 0 ≤ κ ∧ κ < 1 ∧ g ≤ κ ^ 2 + s

/-- A block system with parameters `(g, s, κ)` on the finite set `C` (Definition 4.1).
The Hilbert space `ℒ` (orthogonal to the fixed unit vector `h₀`) is the type `L`; `α = √(1 − κ²)`.
Blocks are indexed by `β` (`blk b ⊆ C`, with vector `ℓ b ∈ ℒ`). The document `v_y = ξ_y + κ h₀` and
the head `u_B = ℓ_B − κ h₀` are not formed explicitly: since `ℓ_B, ξ_y ⊥ h₀` and `‖h₀‖ = 1`,
`⟨u_B, v_y⟩ = ⟨ℓ_B, ξ_y⟩ − κ²`, and the two score conditions are written with that value. -/
structure BlockSystem (L : Type) [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
    (C β : Type) (g s κ : ℝ) where
  params : ValidParams g s κ
  ξ : C → L
  blk : β → Finset C
  ℓ : β → L
  ξ_norm : ∀ y, ‖ξ y‖ = Real.sqrt (1 - κ ^ 2)
  ℓ_norm : ∀ b, ‖ℓ b‖ ≤ Real.sqrt (1 - κ ^ 2)
  score_mem : ∀ b y, y ∈ blk b → s + g ≤ inner ℝ (ℓ b) (ξ y) - κ ^ 2
  score_nmem : ∀ b y, y ∉ blk b → inner ℝ (ℓ b) (ξ y) - κ ^ 2 ≤ s - g

variable {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
  {C β : Type} {g s κ : ℝ}

/-- The score `⟨ℓ − κ h₀, ξ_y + κ h₀⟩ = ⟨ℓ, ξ_y⟩ − κ²` of the head with `ℒ`-part `ℓ` on the
document `v_y`. The null head is `ℓ = 0`, scoring `−κ²`. -/
noncomputable def BlockSystem.score (S : BlockSystem L C β g s κ) (ℓ : L) (y : C) : ℝ :=
  inner ℝ ℓ (S.ξ y) - κ ^ 2

/-- The system is `(M, j)`-regular: the blocks form `j` classes (`cls b` is the class of block `b`),
each class a partition of `C` into blocks of size `M`, and blocks of different classes share at most
one point. -/
def BlockSystem.IsRegular [DecidableEq C] (S : BlockSystem L C β g s κ) (M j : ℕ) : Prop :=
  ∃ cls : β → Fin j, (∀ b, (S.blk b).card = M) ∧
    (∀ c : Fin j, ∀ y : C, ∃! b, cls b = c ∧ y ∈ S.blk b) ∧
    (∀ b b', cls b ≠ cls b' → (S.blk b ∩ S.blk b').card ≤ 1)

/-- `Y ⊆ C` is realized by `r` heads whose `ℒ`-parts satisfy `P`: for every labelling `σ` there are
`ℓ_1, …, ℓ_r ∈ ℒ` of norm at most `α`, each satisfying `P`, with
`max_i ⟨ℓ_i − κ h₀, v_y⟩ ≥ s + g` if `σ_y = +1` and `≤ s − g` if `σ_y = −1`, for every `y ∈ Y`
(`true` is `+1`). -/
def BlockSystem.RealizesWith (S : BlockSystem L C β g s κ) (Y : Finset C) (r : ℕ)
    (P : L → Prop) : Prop :=
  ∀ σ : C → Bool, ∃ ℓs : Fin r → L, (∀ i, ‖ℓs i‖ ≤ Real.sqrt (1 - κ ^ 2)) ∧ (∀ i, P (ℓs i)) ∧
    ∀ y ∈ Y, (σ y = true → ∃ i, s + g ≤ S.score (ℓs i) y) ∧
      (σ y = false → ∀ i, S.score (ℓs i) y ≤ s - g)

/-- `Y` is realized by `r` heads (Definition 4.1's paragraph after the definition). -/
def BlockSystem.Realizes (S : BlockSystem L C β g s κ) (Y : Finset C) (r : ℕ) : Prop :=
  S.RealizesWith Y r fun _ => True

/-- A head is a block head `ℓ_B − κ h₀` or the null head `−κ h₀`. -/
def BlockSystem.BlockOrNull (S : BlockSystem L C β g s κ) (ℓ : L) : Prop :=
  ℓ = 0 ∨ ∃ b, ℓ = S.ℓ b

/-! ### The random sampling of §4 -/

/-- Probability of the subset `X` when each point of `C` is kept independently with probability
`p`: `p^{|X|} (1 − p)^{|C| − |X|}`. -/
noncomputable def bernWeight [Fintype C] (p : ℝ) (X : Finset C) : ℝ :=
  p ^ X.card * (1 - p) ^ (Fintype.card C - X.card)

open Classical in
/-- `Pr[E(X, S)]` for independent random subsets `X` (rate `p`) and `S` (rate `δ`) of `C`: a sum of
point masses over the finite product space. -/
noncomputable def sampleProb [Fintype C] (p δ : ℝ) (E : Finset C → Finset C → Prop) : ℝ :=
  ∑ X : Finset C, ∑ Sm : Finset C, if E X Sm then bernWeight p X * bernWeight δ Sm else 0

/-- A block `b` is chosen if `|B ∩ X| = M₀` and `B ∩ X ⊆ S`. -/
def BlockSystem.Chosen [DecidableEq C] (S : BlockSystem L C β g s κ) (M0 : ℕ)
    (X Sm : Finset C) (b : β) : Prop :=
  (S.blk b ∩ X).card = M0 ∧ S.blk b ∩ X ⊆ Sm

open Classical in
/-- `H`, the number of chosen blocks. -/
noncomputable def BlockSystem.numChosen [Fintype β] [DecidableEq C] (S : BlockSystem L C β g s κ)
    (M0 : ℕ) (X Sm : Finset C) : ℕ :=
  (Finset.univ.filter fun b => S.Chosen M0 X Sm b).card

open Classical in
/-- `U`, the set of points of `X ∩ S` in no chosen block. -/
noncomputable def BlockSystem.uncovered [DecidableEq C] (S : BlockSystem L C β g s κ) (M0 : ℕ)
    (X Sm : Finset C) : Finset C :=
  (X ∩ Sm).filter fun y => ∀ b, S.Chosen M0 X Sm b → y ∉ S.blk b

/-- `π₀ = Pr[Bin(M − 1, p) = M₀ − 1]`. -/
noncomputable def pi0 (M M0 : ℕ) (p : ℝ) : ℝ :=
  ((M - 1).choose (M0 - 1) : ℝ) * p ^ (M0 - 1) * (1 - p) ^ (M - M0)

end MarginMaxima.Critical


