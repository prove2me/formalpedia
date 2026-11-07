-- Prove2me | Definitions.Def_ShallowSym_weight
-- name    : ShallowSym_weight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:20.412356+00:00
-- url     : https://prove2.me/theorems/393dfd44-983a-41ef-9cbe-c305ebdf88a3
-- title:
--   The Boolean hypercube $\{0,1\}^n$ and the Hamming weight $|x|$
-- statement:
--   A Boolean function on $n$ variables maps the hypercube $\{0,1\}^n$ to $\{0,1\}$. For $x\in\{0,1\}^n$, the **Hamming weight** (or weight) $|x|$ is the number of coordinates of $x$ set to $1$:
--
--   $$|x| = \#\{\, i \in \{0,\dots,n-1\} : x_i = 1 \,\}.$$
--
--   These are the basic objects of every statement of the mission.
--
--   **Formalization Note** The cube is `Cube n := Fin n → Bool` (coordinates indexed $0,\dots,n-1$, the bit $1$ is `true`).
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §2 'Functions', p.4

import Mathlib

namespace ShallowSym

/-- The Boolean hypercube `{0,1}^n`, as `Fin n → Bool` (`true` is the bit 1).

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §2 "Functions", p.4: "A Boolean function on n variables maps the hypercube
{0, 1}^n to {0, 1}." -/
abbrev Cube (n : ℕ) : Type := Fin n → Bool

/-- The Hamming weight `|x|` of `x ∈ {0,1}^n`: the number of coordinates set to 1.

V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…), §2 "Functions", p.4: "For x ∈ {0, 1}^n, |x| denotes its Hamming weight (or simply
weight), the number of coordinates of x set to 1." -/
def weight {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

end ShallowSym


