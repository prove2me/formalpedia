-- Prove2me | Definitions.Def_ClassicalSchurColoring
-- name    : ClassicalSchurColoring
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-03T23:56:46.967778+00:00
-- url     : https://prove2.me/theorems/252e2fc1-4067-4a3d-9093-8c5c58566842
-- title:
--   Schur colourings of $[1, N]$ and the colour neighbourhoods of their difference colouring: central and endpoint neighbourhoods
-- statement:
--   This bundle defines Schur colourings of an initial interval and three neighbourhood sets of the difference colouring that a Schur colouring induces. All frontier theorems of the mission are stated with them.
--
--   Throughout, $\mathbb{N} = \{0, 1, 2, \dots\}$, $[a, b] = \{a, a+1, \dots, b\}$, and for $n \in \mathbb{N}$ the $n$ colours are the elements $0, 1, \dots, n-1$ of $\mathrm{Fin}\,n$. The **difference colouring** of a colouring $c : \mathbb{N} \to \mathrm{Fin}\,n$ gives a pair $\{x, y\}$ of distinct naturals the colour $c(|x - y|)$.
--
--   1. Let $N, n \in \mathbb{N}$ and $c : \mathbb{N} \to \mathrm{Fin}\,n$. The colouring $c$ is a **Schur colouring of $[1, N]$** (Lean `SchurColoring N c`) if there are no $x, y \ge 1$ with $x + y \le N$ and $c(x) = c(y) = c(x + y)$. The case $x = y$ is included.
--   2. For a finite set $V \subseteq \mathbb{N}$, a point $v \in \mathbb{N}$ and a colour $i$, the **colour-$i$ neighbourhood of $v$ in $V$** (Lean `colorNbhd c V v i`) is
--   $$
--   \Gamma_i(V, v) = \{\, w \in V : w \ne v,\ c(|v - w|) = i \,\}.
--   $$
--   3. For $m \in \mathbb{N}$, the **central neighbourhood** (Lean `centralNbhd c m`) is the neighbourhood of the centre $m$ of $[0, 2m+1]$ in the colour $c(m+1)$ of its pair with the endpoint $2m + 1$:
--   $$
--   V_m = \Gamma_{c(m+1)}\bigl([0, 2m+1],\, m\bigr) = \{\, x \in [0, 2m+1] : x \ne m,\ c(|m - x|) = c(m+1) \,\}.
--   $$
--   The endpoint $2m + 1$ is always in $V_m$, because $(2m+1) - m = m + 1$.
--   4. For $m \in \mathbb{N}$ and a colour $i$, the **endpoint neighbourhood** (Lean `endpointNbhd c m i`) is the colour-$i$ neighbourhood of the endpoint $2m + 1$ inside $V_m$:
--   $$
--   P_i = \Gamma_i\bigl(V_m,\, 2m+1\bigr) = \{\, x \in V_m : x \ne 2m+1,\ c(2m + 1 - x) = i \,\}.
--   $$
--
--   For example, the three classes $\{1, 4, 7, 10, 13\}$, $\{2, 3, 11, 12\}$ and $\{5, 6, 8, 9\}$ form a Schur colouring of $[1, 13]$ with three colours. For $m = 6$, the colour $c(7)$ is the colour of $\{1, 4, 7, 10, 13\}$, so $V_6 = \{2, 5, 7, 10, 13\}$ (the points at distance $1$, $4$ or $7$ from $6$). The endpoint neighbourhood of the colour of $\{2, 3, 11, 12\}$ is $\{2, 10\}$ (distances $11$ and $3$ from $13$), and that of the colour of $\{5, 6, 8, 9\}$ is $\{5, 7\}$ (distances $8$ and $6$).
--
--   A Schur colouring of $[1, N]$ with $n$ colours gives a cover of $[1, N]$ by $n$ sumfree sets, and for $n \ge 1$ such a cover gives a Schur colouring; the two bridge theorems of the mission state these two directions. The neighbourhoods $V_m$ and $P_i$ are the objects of the frontier analysis of the centred Schur bound: the mission determines $|V_m|$, the colour-$i$ degrees inside $V_m$ for every colour $i \ne c(m+1)$, and the size and symmetry of $P_i$ for every colour $i \ne c(m+1)$, for a Schur colouring of the largest interval that the centred bound does not exclude.
--
--   **Formalization Note.** (1) A colouring is a function on all of $\mathbb{N}$ with values in `Fin n`; `SchurColoring N c` constrains only its values on $[1, N]$. For $n = 0$ there is no function $\mathbb{N} \to \mathrm{Fin}\,0$. (2) The value $c(0)$ never enters a neighbourhood, since $w \ne v$ gives $|v - w| \ge 1$. (3) Distances are Mathlib's `Nat.dist`, which is $|x - y|$ on $\mathbb{N}$. (4) Neighbourhoods are `Finset`s. The ambient set of $V_m$ is `range (2 * m + 2)`, that is $[0, 2m+1]$, so the point $0$ is a candidate member: for $m \ge 1$, $0 \in V_m$ if $c(m) = c(m+1)$, and only then. For $m = 0$ the point $0$ is the centre, and $V_0 = \{1\}$.
-- source:
--   Note "The frontier of the centred Schur bound: balance, saturation and reflection" (schur-numbers project, 2026-10-02, unpublished), sections "Setting" (Schur colourings with x = y allowed, the difference colouring, colour neighbourhoods), "Nested saturation" (the central neighbourhood V, the colour-c(m + 1) neighbourhood of m in [0, 2m + 1]) and "Paired endpoint neighbourhoods" (the endpoint neighbourhoods P_i). Lean proof not yet in a public repository.

-- Generated from lean/ClassicalSchur/Midpoint.lean by skeleton
-- subtraction: every declaration except the def-material below is deleted,
-- and project imports are rewritten to their platform Definitions bundles.
import Mathlib

namespace ClassicalSchur

open Finset

/-- `c` colours `[1, N]` with no monochromatic Schur triple: there are no
`x, y ≥ 1` with `x + y ≤ N` and `c x = c y = c (x + y)`. The case `x = y` is
included. -/
def SchurColoring {n : ℕ} (N : ℕ) (c : ℕ → Fin n) : Prop :=
  ∀ x y, 0 < x → 0 < y → x + y ≤ N → c x = c y → c (x + y) ≠ c x

/-- The colour-`i` neighbourhood of `v` in `V` for the difference colouring of
`c`: the points `w ≠ v` of `V` with `c |v − w| = i`. -/
def colorNbhd {n : ℕ} (c : ℕ → Fin n) (V : Finset ℕ) (v : ℕ) (i : Fin n) : Finset ℕ :=
  (V.erase v).filter fun w => c (Nat.dist v w) = i

/-- The neighbourhood of the centre `m` of `[0, 2m + 1]` in the colour
`c (m + 1)` of its edge to the endpoint `2m + 1`. -/
def centralNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) : Finset ℕ :=
  colorNbhd c (range (2 * m + 2)) m (c (m + 1))

/-- The neighbourhood of the endpoint `2m + 1` of colour `i` inside the
central neighbourhood. -/
def endpointNbhd {n : ℕ} (c : ℕ → Fin n) (m : ℕ) (i : Fin n) : Finset ℕ :=
  colorNbhd c (centralNbhd c m) (2 * m + 1) i

end ClassicalSchur


