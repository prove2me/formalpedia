-- Prove2me | Definitions.Def_ListHashFurstenberg_Main_Furstenberg
-- name    : ListHashFurstenberg_Main_Furstenberg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:39.984299+00:00
-- url     : https://prove2.me/theorems/529241e6-9283-45b3-90e4-2ca339bd1503
-- title:
--   Definition 1.2 — Furstenberg sets $(\delta,n,r,T)$ over a finite field
-- statement:
--   Let $F$ be a finite field with $q=|F|$ elements, $n,r\ge0$ integers, $T$ a real threshold and $S\subseteq F^n$. For an $r$-dimensional linear subspace $V\le F^n$, call $V$ a **rich direction** of $S$ if some translate meets $S$ in at least $T$ points:
--
--   $$\exists\,x\in F^n:\quad |(x+V)\cap S|\ge T.$$
--
--   The **rich fraction** of $S$ is the number of rich $r$-dimensional subspaces divided by the number of all $r$-dimensional subspaces of $F^n$ (the Grassmannian $\mathrm{Gr}(n,r)$). The set $S$ is **$(\delta,n,r,T)$-Furstenberg** if its rich fraction is at least $\delta$.
--
--   With $\delta=1$ and $T=q^r$ this is the notion of an $(n,r)$-Kakeya set. Every lower bound of the mission (Theorem 2.8, Corollaries 2.14 and 2.17, Lemma 2.16, Theorem 2.20) is a statement about this class, and the hashing results of §3 apply it to translates of kernels of linear maps.
--
--   **Formalization Note** The size $|(x+V)\cap S|$ is computed as the number of $s\in S$ with $s-x\in V$, and the fraction is a quotient of cardinalities of finite types (there are finitely many subspaces of $F^n$). If $r>n$ there is no $r$-dimensional subspace and the fraction is $0/0=0$, so for $\delta>0$ no set is Furstenberg. The threshold $T$ is real; a real $T$ means at least $\lceil T\rceil$ points.
-- source:
--   Vinayak M. Kumar, Geoffrey Mon, List Decoding, Linear Hashing, and Furstenberg over F_q, STOC 2027 submission #1578 (October 2026), PDF SHA-256 7cc3a39af88d6de0a57be33c5d8c2855020a7107b6d5e947fb47901273a80ed9, Definition 1.2, p.6; standing notation of §2.1, p.11

import Mathlib

namespace ListHashFurstenberg.Main

open Classical in
/-- **Fraction of rich directions** (Definition 1.2, p.6 of Kumar–Mon, *List Decoding, Linear
Hashing, and Furstenberg over F_q*, STOC 2027 submission #1578): for a finite field `F`, a set
`S ⊆ F^n`, a dimension `r` and a real threshold `T`, the number of `r`-dimensional linear
subspaces `V ≤ F^n` having some translate `x + V` with `|(x + V) ∩ S| ≥ T`, divided by the number
of all `r`-dimensional subspaces of `F^n`.

**Formalization Note** `|(x + V) ∩ S|` is computed as the number of `s ∈ S` with `s - x ∈ V`.
Both counts are cardinalities of finite types (`F^n` has finitely many subspaces). When there
is no `r`-dimensional subspace (`r > n`) the quotient is `0 / 0 = 0`. -/
noncomputable def richFraction {F : Type*} [Field F] [Fintype F] (n r : ℕ) (T : ℝ)
    (S : Finset (Fin n → F)) : ℝ :=
  (Nat.card {V : Submodule F (Fin n → F) // Module.finrank F V = r ∧
      ∃ x : Fin n → F, T ≤ ((S.filter fun s => s - x ∈ V).card : ℝ)} : ℝ) /
    (Nat.card {V : Submodule F (Fin n → F) // Module.finrank F V = r} : ℝ)

/-- **Furstenberg sets** (Definition 1.2, p.6 of Kumar–Mon, STOC 2027 submission #1578):
`S ⊆ F^n` is `(δ, n, r, T)`-Furstenberg if for at least a `δ`-fraction of the `r`-dimensional
linear subspaces `V ≤ F^n` there is a shift `x ∈ F^n` with `|(x + V) ∩ S| ≥ T`. -/
def IsFurstenberg {F : Type*} [Field F] [Fintype F] (δ : ℝ) (n r : ℕ) (T : ℝ)
    (S : Finset (Fin n → F)) : Prop :=
  δ ≤ richFraction n r T S

end ListHashFurstenberg.Main


