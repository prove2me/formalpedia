-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_Config
-- name    : KawasakiSOS_Threshold_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:45.0352+00:00
-- url     : https://prove2.me/theorems/0ddb8af2-c7d9-4f21-9c4a-aa57641a4685
-- title:
--   The state space $\Omega_{n,k}$ of column heights
-- statement:
--   For integers $n\ge 0$ and $k\ge 1$, the state space of the fixed-magnetization solid-on-solid model on the cycle $C_k$ is
--
--   $$\Omega=\Omega_{n,k}=\Bigl\{h\in\mathbb Z_{\ge 0}^{\,k}:\ \sum_{i\in\mathbb Z_k}h(i)=n\Bigr\}.$$
--
--   Columns are indexed by $\mathbb Z_k$, and $h(i)$ is the height of column $i$. The total mass $n$ is the conserved quantity of the dynamics.
--
--   **Formalization Note** Columns are `ZMod k` with `[NeZero k]`, and the type carries a `Fintype` instance. The paper's standing range $2\le k\le n$ is a hypothesis of each theorem, not part of this type.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib

namespace KawasakiSOS.Threshold

/-- The state space `Ω = Ω_{n,k}`: vectors of nonnegative integer column heights indexed by `ℤ_k` with total `n`.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
abbrev Config (n k : ℕ) [NeZero k] : Type := {h : ZMod k → ℕ // ∑ i, h i = n}

/-- `Ω_{n,k}` is finite: every height is at most `n`. -/
noncomputable instance (n k : ℕ) [NeZero k] : Fintype (Config n k) :=
  Fintype.ofInjective
    (fun (h : Config n k) (i : ZMod k) =>
      (⟨h.1 i, by
        have hle := Finset.single_le_sum (f := h.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [h.2] at hle
        omega⟩ : Fin (n + 1)))
    (fun a b hab => Subtype.ext (funext fun i => congrArg Fin.val (congrFun hab i)))

end KawasakiSOS.Threshold


