-- Prove2me | Definitions.Def_HWMaskLeak_wt
-- name    : HWMaskLeak_wt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:29:33.591837+00:00
-- url     : https://prove2.me/theorems/e293e199-53b0-43b2-ae0e-027fcdc96f97
-- title:
--   Hamming weight $\mathrm{wt}(x)$ on $\mathbb Z/N\mathbb Z$ and the weight set $W=\mathrm{wt}(G)$
-- statement:
--   Let $G=\mathbb Z/N\mathbb Z$ and identify every residue with its canonical representative in $\{0,1,\dots,N-1\}$. The **Hamming weight** $\mathrm{wt}(x)$ of $x\in G$ is the number of ones in the binary expansion of this representative. The **weight set** is
--   $$
--   W:=\mathrm{wt}(G)=\{\mathrm{wt}(x): x\in G\}.
--   $$
--
--   These are the leakage values of the paper: each share of an additive sharing leaks its Hamming weight, and the insecurity sums over weight vectors in $W^k$.
--
--   **Formalization Note** The representative is `ZMod.val`; the weight is the sum of the base-2 digits (`Nat.digits 2`). The weight set needs $N\ge1$ (`NeZero N`) so that $G$ is finite.
-- source:
--   Biswas, Hwang, Maji, Shkredov, Ye, When Masks Leak Their Weight: From Additive Sharing to Learning with Physical Rounding, preprint (version of October 31, 2026, sha256 ab686360…), §1.1.1, p.5, and §2.1, p.15

import Mathlib

namespace HWMaskLeak

/-- **Hamming weight on `ℤ/Nℤ`** (Biswas, Hwang, Maji, Shkredov, Ye, *When Masks Leak Their Weight:
From Additive Sharing to Learning with Physical Rounding*, preprint (version of October 31, 2026,
sha256 ab686360…), §1.1.1, p.5, and §2.1, p.15): each residue `x ∈ G = ℤ/Nℤ` is identified with its
canonical representative in `{0, 1, …, N − 1}`, and `wt(x)` is the number of ones in the binary
expansion of that representative.

**Formalization Note** The canonical representative is `ZMod.val`, and the number of ones is the
sum of the base-2 digits (`Nat.digits 2`). -/
def wt (N : ℕ) (x : ZMod N) : ℕ := (Nat.digits 2 x.val).sum

/-- **The weight set `W := wt(G)`** (same preprint, §1.1.1, p.6, after (1), and §2.1, p.15): the set of
Hamming weights taken by the residues of `ℤ/Nℤ`. -/
def weights (N : ℕ) [NeZero N] : Finset ℕ := Finset.univ.image (wt N)

end HWMaskLeak


