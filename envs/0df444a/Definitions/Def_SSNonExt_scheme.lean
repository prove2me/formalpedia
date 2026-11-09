-- Prove2me | Definitions.Def_SSNonExt_scheme
-- name    : SSNonExt_scheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:52:27.801121+00:00
-- url     : https://prove2.me/theorems/d16adfb0-6442-49fc-9700-118a94619cda
-- title:
--   The scheme $\Pi_b$ over $\mathbb F_{2^b}$: keys $\{L,R,C\}\times V$, tagged shares, $F$, $G$ and $\mathrm{Rec}$ (table (1))
-- statement:
--   Let $b\ge2$, $V=\mathbb F_{2^b}$ and $\alpha\in V\setminus\{0,1\}$. The **key set** is $\mathcal K=\{L,R,C\}\times V$; write $L_i,R_i,C_i$ for $(L,i),(R,i),(C,i)$. Both share alphabets are $\{0,1\}\times V$: $x$ stands for $(0,x)$ and $\bar x$ for $(1,x)$, the **tagged** value; the bar is a formal tag, not an operation on $V$. Messages are $m\in V$, and the scheme $\Pi_b$ is
--
--   | key $k$ | $F(m,k)$ | $G(m,k)$ |
--   |---|---|---|
--   | $L_i$ | $i+m$ | $\bar i$ |
--   | $R_i$ | $\bar i$ | $\alpha\cdot i+m$ |
--   | $C_i$ | $i+m$ | $\alpha\cdot i+m$ |
--
--   The **reconstruction map** reads the tags: on $(x,\bar i)$ it outputs $x+i$; on $(\bar i,y)$ it outputs $y+\alpha i$; on two untagged shares $(x,y)$ it outputs $(\alpha x+y)/(\alpha+1)$; on two tagged shares $(\bar x,\bar y)$ it removes the tags and applies the same central rule $(\alpha x+y)/(\alpha+1)$.
--
--   Each share and the reconstruction use a constant number of operations in $\mathbb F_{2^b}$.
--
--   **Formalization Note** $V$ is Mathlib's `GaloisField 2 b`, given classical `Fintype` and `DecidableEq` instances. A share is a pair (tag, value) with `false` = untagged. The pair $(F,G)$ is packaged as a sharing map `Fin 2 → Share b` in the format of Definition 2.1.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), §3, table (1), p.6 (PDF p.6); proof of Lemma 3.1, p.6; proof of Theorem 1.1, §3.2, p.7

import Mathlib

namespace SSNonExt

/-- The field `V = 𝔽_{2^b}` of §3 (p.6), Mathlib's `GaloisField 2 b`.
D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), §3, p.6. -/
abbrev V (b : ℕ) : Type := GaloisField 2 b

/-- `GaloisField 2 b` is finite; this gives it a (classical) `Fintype` structure.

**Formalization Note.** Mathlib provides `Finite (GaloisField 2 b)` but no `Fintype` or
`DecidableEq` instance; both are supplied classically here. -/
noncomputable instance instFintypeV (b : ℕ) : Fintype (V b) := Fintype.ofFinite _

/-- Classical decidable equality on `𝔽_{2^b}`. -/
noncomputable instance instDecEqV (b : ℕ) : DecidableEq (V b) := Classical.decEq _

/-- The three branches `L, R, C` of a key (§3, p.6). -/
inductive Branch
  | L
  | R
  | C
  deriving DecidableEq

/-- `{L, R, C}` is a three-element finite type. -/
instance : Fintype Branch :=
  ⟨{Branch.L, Branch.R, Branch.C}, fun x => by cases x <;> simp⟩

instance : Inhabited Branch := ⟨Branch.L⟩

/-- The key set `𝒦 = {L, R, C} × V` (§3, p.6); `(Branch.L, i)` is `Lᵢ`, and so on. -/
abbrev Key (b : ℕ) : Type := Branch × V b

/-- The share alphabet `{0,1} × V` (§3, p.6): `(false, x)` is the untagged value `x`, `(true, x)` is
the tagged value `x̄`. The bar is a formal tag, not an operation on `V`. -/
abbrev Share (b : ℕ) : Type := Bool × V b

/-- The first share `F(m, k)` of the scheme `Π_b`, table (1), p.6:
`F(m, Lᵢ) = i + m`, `F(m, Rᵢ) = īᵢ` (tagged `i`), `F(m, Cᵢ) = i + m`. -/
noncomputable def F {b : ℕ} (m : V b) : Key b → Share b
  | (.L, i) => (false, i + m)
  | (.R, i) => (true, i)
  | (.C, i) => (false, i + m)

/-- The second share `G(m, k)` of the scheme `Π_b`, table (1), p.6:
`G(m, Lᵢ) = ī` (tagged `i`), `G(m, Rᵢ) = α · i + m`, `G(m, Cᵢ) = α · i + m`. -/
noncomputable def G {b : ℕ} (α : V b) (m : V b) : Key b → Share b
  | (.L, i) => (true, i)
  | (.R, i) => (false, α * i + m)
  | (.C, i) => (false, α * i + m)

/-- The reconstruction map `Rec` of the proof of Lemma 3.1 (p.6), made total.
The pattern of tags identifies the branch:
* `(x, ī)` (only the second share tagged): output `x + i`;
* `(ī, y)` (only the first share tagged): output `y + α · i`;
* `(x, y)` (no tag): output `(α · x + y)/(α + 1)`;
* `(x̄, ȳ)` (both tagged; the fourth branch of the proof of Theorem 1.1, p.7): remove the tags and
  apply the central rule `(α · x + y)/(α + 1)`.

**Formalization Note.** Each case uses at most one multiplication, two additions and one division
in `𝔽_{2^b}` after a branch on the tag bits; this is the paper's "constant number of operations". -/
noncomputable def rec {b : ℕ} (α : V b) : Share b → Share b → V b
  | (false, x), (true, i) => x + i
  | (true, i), (false, y) => y + α * i
  | (false, x), (false, y) => (α * x + y) / (α + 1)
  | (true, x), (true, y) => (α * x + y) / (α + 1)

/-- The two-out-of-two scheme `Π_b` of table (1) as a sharing map `Shr = (F, G)` in the format of
Definition 2.1 (party `0` receives `F`, party `1` receives `G`; p.6 "For t = n = 2 we write F = Shr₁
and G = Shr₂"). -/
noncomputable def scheme {b : ℕ} (α : V b) : V b → Key b → Fin 2 → Share b :=
  fun m k => ![F m k, G α m k]

end SSNonExt


