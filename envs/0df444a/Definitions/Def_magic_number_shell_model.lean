-- Prove2me | Definitions.Def_magic_number_shell_model
-- name    : magic_number_shell_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T15:43:31.992905+00:00
-- url     : https://prove2.me/theorems/fdfc6e09-4c67-46d4-8b38-ad0101419bc8
-- title:
--   Harmonic-oscillator shell-filling model for nuclear magic numbers
-- statement:
--   This bundle fixes the combinatorial model of nuclear shell filling used by every statement in the mission. It follows the shell-model derivation in which the nuclear force is approximated by an isotropic three-dimensional quantum harmonic oscillator.
--
--   1. **Oscillator level.** The energy of the isotropic three-dimensional oscillator depends only on the sum $n = n_x + n_y + n_z$ of the three quantum numbers, so the states at level $n$ are the weak $3$-compositions of $n$:
--   $$L_n \;=\; \{(n_x,n_y,n_z) \in \mathbb{N}^3 \;:\; n_x+n_y+n_z = n\}.$$
--   Elements are ordered triples, so permutations of the same multiset are distinct states.
--
--   2. **Shell capacity.** Each state accommodates two nucleons of a given kind, one per spin orientation, so the shell at level $n$ holds
--   $$C_n \;=\; 2\,|L_n|$$
--   nucleons.
--
--   3. **Cumulative capacity.** Filling every shell of level strictly below $N$ takes
--   $$S_N \;=\; \sum_{n < N} C_n$$
--   nucleons; in particular $S_0 = 0$ and $S_1 = C_0$. The shell-model prediction of a magic number is a value $S_N$.
--
--   4. **Magic numbers.** $M = \{2, 8, 20, 28, 50, 82, 126\}$ is the list of the seven most widely recognized magic numbers of nucleons, transcribed from the source. It is a datum of the mission, not a derived object: no statement here asserts anything about nuclear binding energies or stability.
--
--   **Formalization Note.** $L_n$ is a finite set of triples of natural numbers, cut out of the box $[0,n]^3$ by the equation $n_x+n_y+n_z=n$; the bound is harmless since every solution satisfies it. $C_n$, $S_N$ and the entries of $M$ are natural numbers, and the sum defining $S_N$ ranges over $n = 0, \dots, N-1$.
-- source:
--   Magic number (physics), Wikipedia, section "Derivation" (the 3D harmonic oscillator paragraph: weak 3-compositions counted by stars and bars, factor 2 for spin, cumulative sums 2, 8, 20, 40), and section lead (list of the seven magic numbers 2, 8, 20, 28, 50, 82, 126). https://en.wikipedia.org/wiki/Magic_number_(physics)

import Mathlib

namespace MagicNumberShellModel

open Finset

/-- States of the isotropic three-dimensional quantum harmonic oscillator at
energy level `n`: the triples `(nx, ny, nz)` of nonnegative integers with
`nx + ny + nz = n` (the weak 3-compositions of `n`). -/
def oscillatorLevel (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1)).filter
    fun p => p.1 + p.2.1 + p.2.2 = n

/-- Number of nucleons filling the oscillator shell of energy level `n`: the
number of states at that level, doubled to account for the two spin
orientations. -/
def shellCapacity (n : ℕ) : ℕ := 2 * (oscillatorLevel n).card

/-- Number of nucleons needed to fill every oscillator shell of energy level
below `N`. -/
def cumulativeCapacity (N : ℕ) : ℕ := ∑ n ∈ range N, shellCapacity n

/-- The seven most widely recognized magic numbers of nucleons. -/
def magicNumbers : Finset ℕ := {2, 8, 20, 28, 50, 82, 126}

end MagicNumberShellModel


