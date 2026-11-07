-- Prove2me | Definitions.Def_MultiSelectPandora_DPData_value
-- name    : MultiSelectPandora_DPData_value
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:08.220206+00:00
-- url     : https://prove2.me/theorems/8527d932-431d-44df-89e0-f20803be1a32
-- title:
--   The continuation value $G_J(U,\alpha)$
-- statement:
--   $G_J(U,\alpha)$ is the largest expected total reward on $J$ of a continuation that starts from $\alpha$ and uses only actions on the boxes in $U$:
--   $$G_J(U,\alpha)=\max\Big\{0,\ \max_{i\in U}\sum_j\mathrm{prob}_{ij}\big(g(\alpha,a_i^0)+G_J(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{x_{ij}\}))\big),\ \max_{i\in U}\big(g(\alpha,a_i^1)+G_J(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{b_i\}))\big)\Big\}.$$
--   The term $0$ is the action *end*, repeated. Only the continuation reward counts, not the entries of $\alpha$. $\mathrm{OPT}_J$ is $G_J(M,0)$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Definition 3.27, p.16 (PDF p.17); Bellman's equation, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_DPData
import Definitions.Def_MultiSelectPandora_DPData_openGain
import Definitions.Def_MultiSelectPandora_DPData_claimGain
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **The continuation value `G_J(U, α)`.** Beyhaghi–Han–Luqman manuscript, Definition 3.27, p.16 (PDF p.17): "the largest
expected total reward on `J` of a continuation that starts from `α` and uses only actions on the boxes in `U`"; Bellman's
equation, p.8 (PDF p.9).

**Formalization Note.** Only the continuation reward counts. The `max` includes `0` (the action `end`, repeated). `go`
recurses on a fuel equal to `|U|`. Each box is used at most once, by opening or by a closed claim. -/
noncomputable def DPData.value {n : ℕ} {s : Fin n → ℕ} (J : DPData n s) {k : ℕ} (U : Finset (Fin n)) (α : Fin k → ℝ) : ℝ :=
  go U.card U α
where
  /-- the recursion, with fuel `|U|` -/
  go : ℕ → Finset (Fin n) → (Fin k → ℝ) → ℝ
    | 0, _, _ => 0
    | m + 1, U, α =>
      U.fold max 0 fun i =>
        max (∑ j, J.prob i j * (J.openGain α i j + go m (U.erase i) (insertTop α (J.x i j))))
          (J.claimGain α i + go m (U.erase i) (insertTop α (J.b i)))

end MultiSelectPandora


