-- Prove2me | Definitions.Def_AgriSubsidy_Combined_Majorization
-- name    : AgriSubsidy_Combined_Majorization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:54.85376+00:00
-- url     : https://prove2.me/theorems/da369227-b0be-4d74-b177-bfeb3606d261
-- title:
--   Definition 1, p. 9 — majorization and weak sub-majorization of finite vectors
-- statement:
--   For a finite vector $u$, let $T_k(u)$ be the largest sum of $k$ distinct coordinates, for $0\le k\le N$. The order $u\ge_{wm}v$ means $T_k(u)\ge T_k(v)$ for every such $k$. The majorization order $u\ge^m v$ adds equality of the total coordinate sums.
--
--   $$u\ge^m v\quad\Longleftrightarrow\quad (\forall k\le N,\ T_k(u)\ge T_k(v))\ \text{and}\ \sum_j u_j=\sum_j v_j.$$
--
--   This order measures dispersion: a vector with greater top-coordinate sums and the same total is more dispersed. It is the comparison used for farmer productivity, output, and profit changes.
--
--   **Formalization Note** The empty selection has sum zero; the order tests it as the harmless $k=0$ case. The top-sum function returns zero outside $k\le N$, where the order never uses it. Farmer indices start at zero in Lean.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), p. 9, Definition 1

import Mathlib

namespace AgriSubsidy.Combined

noncomputable def topSum {N : ℕ} (u : Fin N → ℝ) (k : ℕ) : ℝ :=
  if hk : k ≤ N then
    (Finset.univ.powersetCard k).sup'
      (Finset.powersetCard_nonempty.mpr (by simpa using hk))
      (fun S => ∑ i ∈ S, u i)
  else 0

def WeakSubMaj {N : ℕ} (u v : Fin N → ℝ) : Prop :=
  ∀ k, k ≤ N → topSum v k ≤ topSum u k

def Majorizes {N : ℕ} (u v : Fin N → ℝ) : Prop :=
  WeakSubMaj u v ∧ ∑ j, u j = ∑ j, v j

end AgriSubsidy.Combined


