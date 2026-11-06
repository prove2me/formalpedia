-- Prove2me | Definitions.Def_MemQueryFeas_pathOracle
-- name    : MemQueryFeas_pathOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:36:37.224209+00:00
-- url     : https://prove2.me/theorems/596c17a7-05dc-4e91-a61b-38359be5ef26
-- title:
--   Path separation oracle $O_\ell$ (Algorithm 3)
-- statement:
--   For a leaf $\ell=(\ell_1,\dots,\ell_P)\in V_P$ with ancestors $v_p=(\ell_1,\dots,\ell_p)$, the path oracle answers a query $x$ as follows:
--   1. if $e^\top x>-1/2$, answer $e$;
--   2. otherwise, for $p=1,\dots,P$: if $\|P_{E_{v_p}}(T_{v_{p-1}}x)\|>\delta_{v_p}$, answer $T_{v_{p-1}}^\top P_{E_{v_p}}(T_{v_{p-1}}x)$;
--   3. otherwise answer Success.
--
--   Here $E_{v_p}=E^{(\ell_p)}_{v_{p-1},p}$ and $\delta_{v_p}=\delta_p^{(\ell_p)}$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 3, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_Tmap
import Definitions.Def_MemQueryFeas_eVec

namespace MemQueryFeas

/-- **Path separation oracle `O_ℓ` (Algorithm 3).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 3, p.9 (PDF p.10): "Input: query
`x`. 1 if `e^⊤x > −1/2` then Answer `x` with `e`; 2 Denote by `v_p = (ℓ_1, …, ℓ_p)` the layer-`p`
ancestor of `ℓ`; 3 for `p = 1, …, P` do 4 if `‖P_{E_{v_p}}(T_{v_{p−1}}(x))‖ > δ_{v_p}` then return
`T_{v_{p−1}}^⊤ P_{E_{v_p}}(T_{v_{p−1}}(x))`; 5 return Success."

For a leaf `ℓ = (ℓ_1, …, ℓ_P)`, realized versions `c p v' i = E^(i)_{v',p}` and accuracies
`δ p i = δ_p^(i)`: `E_{v_p} = c p v_{p−1} ℓ_p`, `δ_{v_p} = δ p ℓ_p`, `T_{v_{p−1}} = Tmap δ c v_{p−1}`.
The oracle returns `some e` if `⟪e, x⟫ > −1/2`; otherwise `some (T^⊤ P_E T x)` for the first layer
whose test fails; otherwise Success (`none`).

**Formalization Note.** `T^⊤` is the adjoint. Layers are scanned in the order `p = 1, …, P`
(list positions `0, …, P−1`). -/
noncomputable def pathOracle {d : ℕ} (δ : ℕ → ℕ → ℝ) (c : ℕ → List ℕ → ℕ → Op d)
    (ℓ : List ℕ) (x : Vec d) : Option (Vec d) :=
  if -1 / 2 < inner ℝ (eVec d) x then some (eVec d) else
    match (List.range ℓ.length).find? (fun s =>
        decide (δ (s + 1) (ℓ.getD s 0) <
          ‖c (s + 1) (ℓ.take s) (ℓ.getD s 0) (Tmap δ c (ℓ.take s) x)‖)) with
    | some s => some (ContinuousLinearMap.adjoint (Tmap δ c (ℓ.take s))
        (c (s + 1) (ℓ.take s) (ℓ.getD s 0) (Tmap δ c (ℓ.take s) x)))
    | none => none

end MemQueryFeas


