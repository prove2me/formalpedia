-- Prove2me | Definitions.Def_ElimAgree_nuDisj
-- name    : ElimAgree_nuDisj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:31:12.087284+00:00
-- url     : https://prove2.me/theorems/3ad01c49-5f80-4264-af9e-f400607823c8
-- title:
--   The laws $\nu_z$ of the proof of Theorem 3.8
-- statement:
--   For $n\ge3$ let $\ell=\lfloor(n+1)/4\rfloor$ and $N=4\ell-1\le n$. Restrict all instances to the first $N$ elements of $[n]$. For $z\in\{0,1\}^k$ let $\nu_z=\mu_\sigma$ with $\sigma_i=D$ if $z_i=1$ and $\sigma_i=I$ otherwise, viewed as a law on pairs $(X,Y)$ of $k$-tuples of subsets of $[n]$ through the inclusion $[N]\subseteq[n]$. In particular $\nu_{(1,\dots,1)}=\mu_D^{\otimes k}=\lambda$.
--
--   These laws feed Theorem 3.1 in the proof of Theorem 3.8.
--
--   **Formalization Note** $\nu_z$ is the pushforward of $\mu_z$ along the injective map that embeds each set; the inclusion is `Fin.castLE`. With `true` $=D$ and $\mathrm{DISJ}=1$ as `true`, $\sigma=z$.
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), proof of Theorem 3.8, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ElimAgree_disjAns
import Definitions.Def_ElimAgree_muD

namespace ElimAgree

/-- `ℓ = ⌊(n + 1)/4⌋` (Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of
Agreement in Elimination*, manuscript, STOC 2027 submission, Theorem 3.8, p.10). -/
def ell (n : ℕ) : ℕ := (n + 1) / 4

/-- `N = 4ℓ − 1 ≤ n` for `ℓ = ⌊(n + 1)/4⌋`. -/
theorem fourEll_sub_one_le (n : ℕ) : 4 * ell n - 1 ≤ n := by
  unfold ell; omega

/-- A subset of the first `N = 4ℓ − 1` elements, viewed as a subset of `[n]`. -/
def embedN (n : ℕ) (S : Nset (ell n)) : Finset (Fin n) :=
  S.map (Fin.castLEEmb (fourEll_sub_one_le n))

/-- The laws `ν_z` of the proof of Theorem 3.8 (p.10): restrict all instances to the first
`N = 4ℓ − 1 ≤ n` elements and let `ν_z = µ_σ` with `σ_i = D` iff `z_i = 1`, pushed forward to
`Inp n k × Inp n k` along the inclusion `[N] ⊆ [n]`.

**Formalization Note.** With `true = D` and `DISJ = 1 = true`, `σ = z`. The pushforward of a law
`μ` along the injective map `e` is `Σ_{q : e q = p} μ q`. -/
noncomputable def nuDisj (n k : ℕ) (z : Fin k → Bool) : Inp n k × Inp n k → ℝ :=
  fun p => ∑ q : (Fin k → Nset (ell n)) × (Fin k → Nset (ell n)),
    if (fun i => embedN n (q.1 i)) = p.1 ∧ (fun i => embedN n (q.2 i)) = p.2
    then muSigma (ell n) z q else 0

end ElimAgree


