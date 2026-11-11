-- Prove2me | Definitions.Def_OptLocalHamSim_suzuki
-- name    : OptLocalHamSim_suzuki
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:55.205909+00:00
-- url     : https://prove2.me/theorems/41cef531-67fa-4dc0-b68b-d0168c7668cf
-- title:
--   Suzuki product formula $C=S_p$ (Eqs. (20)–(21)) and the commutator sum $\alpha_{\mathrm{com}}$ (Eq. (22))
-- statement:
--   For color Hamiltonians $H_1,\dots,H_c$, the symmetric second-order formula is
--
--   $$
--   S_2(s):=e^{-iH_1s/2}\cdots e^{-iH_cs/2}\,e^{-iH_cs/2}\cdots e^{-iH_1s/2},
--   $$
--
--   and Suzuki's recursion is
--
--   $$
--   S_{2k}(s):=S_{2k-2}(a_ks)^2\,S_{2k-2}\bigl((1-4a_k)s\bigr)\,S_{2k-2}(a_ks)^2,\qquad a_k:=\bigl(4-4^{1/(2k-1)}\bigr)^{-1},
--   $$
--
--   for $k\ge2$; the product formula of even order $p$ is $C:=S_p$. For local summands $F_a$,
--
--   $$
--   \alpha_{\mathrm{com}}:=\sum_{a_1,\dots,a_{p+1}}\bigl\|[F_{a_{p+1}},\dots,[F_{a_2},F_{a_1}]\dots]\bigr\| .
--   $$
--
--   These are the product formula whose error Lemma 6 bounds and whose residual Lemma 7 expands.
--
--   **Formalization Note** $C$ is defined by the recursion (21) directly, not in the combined-stage form (20). Colors are indexed from $0$.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §3.1, eqs. (20)–(22), pp.14–15

import Mathlib
import Definitions.Def_OptLocalHamSim_IsLocalHam

namespace OptLocalHamSim

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

/-- The symmetric second-order formula of eq. (21), p.15:
`S₂(s) := e^{−iH₁s/2} ⋯ e^{−iH_c s/2} e^{−iH_c s/2} ⋯ e^{−iH₁s/2}` for the color Hamiltonians
`H₁, …, H_c` (Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held version, sha256 44a9768a…).

**Formalization Note** The colors `1, …, c` are `Fin c`; the leftmost factor is the last applied. -/
noncomputable def suzuki2 (Hc : Fin c → Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (List.ofFn fun j => evol (Hc j) (s / 2)).prod * (List.ofFn fun j => evol (Hc j) (s / 2)).reverse.prod

/-- The Suzuki coefficient `a_k := (4 − 4^{1/(2k−1)})⁻¹` of eq. (21). -/
noncomputable def suzukiCoeff (k : ℕ) : ℝ := (4 - (4 : ℝ) ^ ((1 : ℝ) / (2 * k - 1)))⁻¹

/-- `suzukiAux Hc k = S_{2(k+1)}`: the recursion (21),
`S_{2k}(s) := S_{2k−2}(a_k s)² S_{2k−2}((1 − 4a_k)s) S_{2k−2}(a_k s)²`, starting from `S₂`. -/
noncomputable def suzukiAux (Hc : Fin c → Matrix n n ℂ) : ℕ → ℝ → Matrix n n ℂ
  | 0, s => suzuki2 Hc s
  | k + 1, s =>
    let a := suzukiCoeff (k + 2)
    suzukiAux Hc k (a * s) ^ 2 * suzukiAux Hc k ((1 - 4 * a) * s) * suzukiAux Hc k (a * s) ^ 2

/-- **The product formula `C := S_p` of eqs. (20)–(21)**, p.14–15, for an even order `p ≥ 2`:
`S_p = suzukiAux Hc (p/2 − 1)`. Stated directly by the recursion (21), not in the combined-stage
form (20). -/
noncomputable def suzuki (Hc : Fin c → Matrix n n ℂ) (p : ℕ) (s : ℝ) : Matrix n n ℂ :=
  suzukiAux Hc (p / 2 - 1) s

/-- The nested commutator `[F_{a_{k+1}}, …, [F_{a_2}, F_{a_1}] …]` of eq. (22), with `a 0 = a_1`
innermost. -/
def nestedComm {ι : Type} (F : ι → Matrix n n ℂ) : (k : ℕ) → (Fin (k + 1) → ι) → Matrix n n ℂ
  | 0, a => F (a 0)
  | k + 1, a =>
    F (a (Fin.last (k + 1))) * nestedComm F k (fun i => a i.castSucc) -
      nestedComm F k (fun i => a i.castSucc) * F (a (Fin.last (k + 1)))

open scoped Matrix.Norms.L2Operator in
/-- `α_com := ∑_{a_1,…,a_{p+1}} ‖[F_{a_{p+1}}, …, [F_{a_2}, F_{a_1}] …]‖`, eq. (22), p.15. -/
noncomputable def alphaCom {ι : Type} [Fintype ι] (F : ι → Matrix n n ℂ) (p : ℕ) : ℝ :=
  ∑ a : Fin (p + 1) → ι, ‖nestedComm F p a‖

end OptLocalHamSim


