-- Prove2me | Definitions.Def_NoisyOWMPC_Supplement_periodic
-- name    : NoisyOWMPC_Supplement_periodic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:59:42.157197+00:00
-- url     : https://prove2.me/theorems/d466c4f9-832c-4564-a497-fed14a9217bb
-- title:
--   The periodic predicate $\mathrm{Mod}_P$ and the period $P_t$
-- statement:
--   For a positive integer $P$, the **periodic predicate** is
--   $$
--   \mathrm{Mod}_P(z) = \mathbf 1\big[z \bmod P < P/2\big], \qquad z \in \mathbb Z,
--   $$
--   with residues in $\{0, \dots, P-1\}$. The **period** used by the verifiable release test and the verifiable selector is $P_t = 4\lceil t^{9/20}/4\rceil$. An integer $z$ is **at distance at least $b$** from the integers with $\mathrm{Mod}_P = c$ if $|z - z'| \ge b$ for every such $z'$; this is the distance $\mathrm{dist}(\cdot, A_t)$ of (F.3) for $c = 1$ and the robustness distance $d_P$ of Construction F.12 for $c$ the opposite row bit.
--
--   These are shared by Constructions F.2 and F.12.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), §F.1 Parameters and row test, p.68; §F.2 Parameters and row predicate, pp.72–73

import Mathlib

namespace NoisyOWMPC.Supplement

/-- The **periodic predicate** `Mod_P(z) = 1[z mod P < P/2]`, residues in `{0, …, P − 1}` (Ishai,
Lu, Zafar, STOC 2027 submission (manuscript sha256 3a9569fa…), §F.1 Parameters and row test, p.68),
written as `2 (z mod P) < P`. -/
def modP (P : ℕ) (z : ℤ) : Bool := decide (2 * (z % (P : ℤ)) < (P : ℤ))

/-- The **period** `P_t = 4⌈t^{9/20}/4⌉` (p.68; `P_n` on p.73). -/
noncomputable def pPer (t : ℕ) : ℕ := 4 * ⌈(t : ℝ) ^ ((9 : ℝ) / 20) / 4⌉₊

/-- The integer `z` is **at distance at least `b` from every integer `z′` with `Mod_P(z′) = c`**:
`min{|z − z′| : Mod_P(z′) = c} ≥ b` (the distance `dist(·, A_t)` of (F.3), p.68, for `c = 1`, and
`d_P` of p.73 for `c ≠ Mod_P(z)`); for an empty set of such `z′` the condition holds. -/
def FarFrom (P : ℕ) (c : Bool) (b : ℕ) (z : ℤ) : Prop :=
  ∀ z' : ℤ, modP P z' = c → (b : ℤ) ≤ |z - z'|

end NoisyOWMPC.Supplement


