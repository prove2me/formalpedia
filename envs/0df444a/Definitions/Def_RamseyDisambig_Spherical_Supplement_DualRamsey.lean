-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Supplement_DualRamsey
-- name    : RamseyDisambig_Spherical_Supplement_DualRamsey
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:24:43.906303+00:00
-- url     : https://prove2.me/theorems/62044582-19b7-40e0-9e84-01aa294c40a8
-- title:
--   Equipartitions, profiles, rigid surjections and the dual Ramsey conjectures 7, 27, 30
-- statement:
--   A **$k$-equipartition** of $[n]$ is a partition of $[n]$ into $k$ nonempty parts of equal size; a partition $Q$ **coarsens** $P$ if every part of $P$ lies inside a part of $Q$. The **Homogeneous Dual Ramsey Conjecture** (Conjecture 7, Kechris–Sokić–Todorčević) is the proposition: for all $k,m$ with $k\mid m$ and every $r$, there is $n$ divisible by $m$ such that for every $r$-coloring of the $k$-equipartitions of $[n]$ some $m$-equipartition $P$ has all $k$-equipartitions coarsening $P$ of the same color.
--
--   A **profile** is a vector $\alpha=(\alpha_1,\dots,\alpha_s)$ of positive rationals summing to $1$, with $p(\alpha)=s$. A **rigid surjection** $\pi:[n]\to[s]$ is a surjection with $\min\pi^{-1}(1)<\dots<\min\pi^{-1}(s)$; it encodes a canonically ordered partition. An **$\alpha$-partition** of $[n]$ is a rigid surjection $\pi:[n]\to[p(\alpha)]$ with $|\pi^{-1}(j)|/n=\alpha_j$ for all $j$. A **copy of $\beta$ in $\alpha$** is a rigid surjection $\psi:[p(\alpha)]\to[p(\beta)]$ with
--   $$\sum_{i\in\psi^{-1}(j)}\alpha_i=\beta_j\qquad\text{for every }j,$$
--   and $\alpha$ **refines** $\beta$ when such a copy exists.
--
--   The **Profile Dual Ramsey Conjecture** (Conjecture 30): for profiles $\alpha,\beta$ with $\beta$ refining $\alpha$ and every $r$ there is $N$ such that every $r$-coloring of the $\alpha$-partitions of $[N]$ admits a $\beta$-partition $\pi$ of $[N]$ all of whose $\alpha$-partition coarsenings have the same color. The **Multi-Profile Dual Ramsey Conjecture** (Conjecture 27) is the same with profiles $\alpha^{(1)},\dots,\alpha^{(s)}$, all refined by $\beta$, and colorings $c_1,\dots,c_s$: one $\beta$-partition $\pi$ works for all $i$ at once, the color depending on $i$.
--
--   These propositions are defined, never assumed; Lemmas 31, 32, 34, 35 and Theorem 21 are implications between them.
--
--   **Formalization Note** $[n]$ is `Fin n` (0-based). Equipartitions are Mathlib `Finpartition`s of `Finset.univ` (parts are nonempty); coarsening is Mathlib's refinement order `P ≤ Q`. This is not Mathlib's `Finpartition.IsEquipartition`, which allows part sizes differing by one. Profiles and partitions use `Fin`-indexed vectors and maps `Fin n → Fin s`; the minimum of a fibre is `Finset.min` in `WithTop`. "Obtained by coarsening $\pi$" is $\sigma=\psi\circ\pi$ for some map $\psi$. Colorings with $r$ colors take values in `Fin r`, and $k,m,r,s$ are positive integers.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Conjectures 6–7, pp. 6, 24; §A.3, p. 27; Conjecture 27, p. 28; Conjecture 30, p. 30 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical.Supplement

open Finset

/-- A `k`-equipartition of `[n]` (pp. 6, 24): a partition of `[n]` (here `Fin n`) into exactly
`k` nonempty parts (Mathlib's `Finpartition` parts are nonempty) of equal size. Not Mathlib's
`Finpartition.IsEquipartition`, which allows sizes differing by one. -/
def IsKEquipartition {n : ℕ} (k : ℕ) (P : Finpartition (univ : Finset (Fin n))) : Prop :=
  P.parts.card = k ∧ ∀ p ∈ P.parts, ∀ q ∈ P.parts, p.card = q.card

/-- Conjecture 7 (Homogeneous Dual Ramsey, Kechris–Sokić–Todorčević), pp. 6, 24, as a
proposition (never assumed): for positive `k, m` with `k ∣ m` and every positive `r` there is
`n`, divisible by `m`, such that for every `r`-coloring of the `k`-equipartitions of `[n]` there
is an `m`-equipartition `P` such that all `k`-equipartitions coarsening `P` have the same color.
`P ≤ Q` is Mathlib's refinement order: every part of `P` lies in a part of `Q`, i.e. `Q` is
obtained from `P` by merging parts. -/
def HomogeneousDualRamsey : Prop :=
  ∀ k m : ℕ, 0 < k → 0 < m → k ∣ m → ∀ r : ℕ, 0 < r →
    ∃ n : ℕ, m ∣ n ∧
      ∀ col : {Q : Finpartition (univ : Finset (Fin n)) // IsKEquipartition k Q} → Fin r,
        ∃ P : Finpartition (univ : Finset (Fin n)), IsKEquipartition m P ∧
          ∀ Q Q' : {Q : Finpartition (univ : Finset (Fin n)) // IsKEquipartition k Q},
            P ≤ Q.1 → P ≤ Q'.1 → col Q = col Q'

/-- A profile (p. 27): a finite vector `(α_1, …, α_s)` of positive rationals summing to 1;
`len` is `p(α) = s`. Entries are indexed by `Fin s` (0-based). -/
structure Profile where
  len : ℕ
  val : Fin len → ℚ
  pos : ∀ i, 0 < val i
  sum_one : ∑ i, val i = 1

/-- The fibre `π⁻¹(j)`. -/
def fiber {n t : ℕ} (π : Fin n → Fin t) (j : Fin t) : Finset (Fin n) :=
  univ.filter (fun i => π i = j)

/-- A rigid surjection `π : [n] → [t]` (p. 27): surjective with
`min π⁻¹(1) < … < min π⁻¹(t)` (with the order of `Fin`). -/
def IsRigidSurjection {n t : ℕ} (π : Fin n → Fin t) : Prop :=
  Function.Surjective π ∧ StrictMono (fun j : Fin t => (fiber π j).min)

/-- A copy of `β` in `α` (p. 27): a rigid surjection `ψ : [p(α)] → [p(β)]` with
`∑_{i ∈ ψ⁻¹(j)} α_i = β_j` for every `j`. -/
def IsProfileCopy (β α : Profile) (ψ : Fin α.len → Fin β.len) : Prop :=
  IsRigidSurjection ψ ∧ ∀ j : Fin β.len, ∑ i ∈ fiber ψ j, α.val i = β.val j

/-- `α` refines `β` (p. 27): there is a copy of `β` in `α`. -/
def ProfileRefines (α β : Profile) : Prop :=
  ∃ ψ : Fin α.len → Fin β.len, IsProfileCopy β α ψ

/-- An `α`-partition of `[N]` (p. 27): a rigid surjection `π : [N] → [p(α)]` (a canonically
ordered partition) with `|π⁻¹(j)| / N = α_j` for every `j`. -/
def IsProfilePartition (α : Profile) (N : ℕ) (π : Fin N → Fin α.len) : Prop :=
  IsRigidSurjection π ∧ ∀ j : Fin α.len, ((fiber π j).card : ℚ) / N = α.val j

/-- `σ` is obtained by coarsening `π` (p. 27): every part of `π` lies inside a part of `σ`,
i.e. `σ = ψ ∘ π` for some map `ψ` merging the parts of `π`. -/
def Coarsens {N s t : ℕ} (σ : Fin N → Fin s) (π : Fin N → Fin t) : Prop :=
  ∃ ψ : Fin t → Fin s, σ = ψ ∘ π

/-- Conjecture 30 (Profile Dual Ramsey), p. 30, as a proposition (never assumed): for
profiles `α, β` with `β` refining `α` and every positive `r` there is `N` such that every
`r`-coloring of the `α`-partitions of `[N]` admits a `β`-partition `π` of `[N]` all of whose
`α`-coarsenings have the same color. -/
def ProfileDualRamsey : Prop :=
  ∀ α β : Profile, ProfileRefines β α → ∀ r : ℕ, 0 < r → ∃ N : ℕ,
    ∀ c : {σ : Fin N → Fin α.len // IsProfilePartition α N σ} → Fin r,
      ∃ π : Fin N → Fin β.len, IsProfilePartition β N π ∧
        ∀ σ σ' : {σ : Fin N → Fin α.len // IsProfilePartition α N σ},
          Coarsens σ.1 π → Coarsens σ'.1 π → c σ = c σ'

/-- Conjecture 27 (Multi-Profile Dual Ramsey), p. 28, as a proposition (never assumed): for
`s ≥ 1` profiles `α⁽¹⁾, …, α⁽ˢ⁾` and a profile `β` refining each of them, and every positive
`r`, there is `N` such that for any `r`-colorings `c_i` of the `α⁽ⁱ⁾`-partitions of `[N]` some
`β`-partition `π` of `[N]` has, for every `i`, all its `α⁽ⁱ⁾`-coarsenings of the same color
under `c_i` (the color may depend on `i`). -/
def MultiProfileDualRamsey : Prop :=
  ∀ s : ℕ, 0 < s → ∀ (α : Fin s → Profile) (β : Profile), (∀ i, ProfileRefines β (α i)) →
    ∀ r : ℕ, 0 < r → ∃ N : ℕ,
      ∀ c : (i : Fin s) → {σ : Fin N → Fin (α i).len // IsProfilePartition (α i) N σ} → Fin r,
        ∃ π : Fin N → Fin β.len, IsProfilePartition β N π ∧
          ∀ (i : Fin s) (σ σ' : {σ : Fin N → Fin (α i).len // IsProfilePartition (α i) N σ}),
            Coarsens σ.1 π → Coarsens σ'.1 π → c i σ = c i σ'

end RamseyDisambig.Spherical.Supplement


