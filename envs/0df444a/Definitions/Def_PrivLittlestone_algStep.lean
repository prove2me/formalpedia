-- Prove2me | Definitions.Def_PrivLittlestone_algStep
-- name    : PrivLittlestone_algStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:38:52.557333+00:00
-- url     : https://prove2.me/theorems/75f56688-1336-48b2-bc24-42110b86122b
-- title:
--   One round of Algorithm 1
-- statement:
--   **One round of Algorithm 1.** After the record $z_t = (x_t, y_t)$ arrives (the classifier $g$ having been released), set $e = \mathbf 1\{g(x_t) \neq y_t\}$ and $c \leftarrow c + e$; if $e = 1$ and $\kappa(g, z_t) \ne \bot$, append $\kappa(g, z_t)$ to $S$. With the fresh noise $\nu_t \sim \mathrm{Lap}(4/\varepsilon_a)$ and the phase threshold noise $\xi_j \sim \mathrm{Lap}(2/\varepsilon_a)$: if $c + \nu_t \ge U + \xi_j$, the phase ends; the next phase starts at the next round with $c = 0$ and a fresh aggregate sampled from the current $S$, unless the cap of $K$ phases (counting the initial one) is reached, in which case the public fallback $g_{\mathrm{fb}}$ is released on every remaining round and records are discarded. Otherwise the phase continues.
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Algorithm 1, lines 9–20, p.7

import Mathlib
import Definitions.Def_PrivLittlestone_AlgState
import Definitions.Def_PrivLittlestone_sampleAgg

namespace PrivLittlestone

/-- **One round of Algorithm 1** (He–He, *Private Online Learning of Littlestone Classes and
Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562), Algorithm 1, lines 10–16
and 18–20, p.7): after the record `z_t = (x_t, y_t)` of the 0-based round `t` arrives, set
`e = 1{g(x_t) ≠ y_t}`, `c ← c + e`; if `e = 1` and `κ(g, z_t) ≠ ⊥`, append `κ(g, z_t)` to `S`; with
the fresh noise `ν_t ∼ Lap(4/ε_a)` and the phase threshold noise `ξ_j ∼ Lap(2/ε_a)`, if
`c + ν_t ≥ U + ξ_j` the phase ends and the next phase starts at round `t + 1` with `c = 0` and a
fresh aggregate sampled from the current `S`, or, if the cap of `K` phases (counting the initial
one) is reached, the public fallback `g_fb` is released on every remaining round and records are
discarded.

**Formalization Note** Rounds `t ≥ T` read the noise `0` and are never used. -/
noncomputable def algStep {X Z U : Type*} {D : ℕ} {B : ℝ} (P : Alg1Spec X Z U D B)
    (ω : Alg1Coins P) (t : ℕ) (z : X × Bool) (st : AlgState X Z) : AlgState X Z :=
  if st.fallback then st else
    let e : Bool := decide (st.current z.1 ≠ z.2)
    let c' := st.counter + (if e then 1 else 0)
    let S' := if e then (match P.κ st.current z with
                         | some u => st.retained ++ [u]
                         | none => st.retained) else st.retained
    let ν : ℝ := if h : t < P.T then ω.2.2 ⟨t, h⟩ else 0
    let ξ : ℝ := if h : st.phase < P.K then ω.2.1 ⟨st.phase, h⟩ else 0
    if P.Uth + ξ ≤ (c' : ℝ) + ν then
      if st.phase + 1 < P.K then
        { phase := st.phase + 1, start := t + 1, retained := S', counter := 0,
          current := sampleAgg P ω (st.phase + 1) S', fallback := false }
      else
        { st with retained := S', counter := c', current := P.gfb, fallback := true }
    else
      { st with retained := S', counter := c' }

end PrivLittlestone


