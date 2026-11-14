-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling
-- name    : BCFGJPSSV26_Stable_Alg_ClusterSampling
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:39.647665+00:00
-- url     : https://prove2.me/theorems/5079bd7c-7255-4e94-9f04-569bc50ca971
-- title:
--   BCFGJPSSV26.Stable.Alg.ClusterSampling — Cluster sampling
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.ClusterSampling` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Algorithm 2] as a state machine reading one chunk per step
--   (`BCFGJPSSV26.Stable.ksStep`, `BCFGJPSSV26.Stable.ksRun`). The state
--   (`BCFGJPSSV26.Stable.KSState`) is the phase (`0`, `1`, or `2` when done), the outer counter `j`,
--   the deleted centers `R⁻`, the dummies `Λ₂`, and the mode: `START`, `SAMPLE`, `RADD ℓ`, `DG ℓ`,
--   `RG ℓ r₀`, `RGB ℓ r₀`, coded by a tag `0, …, 5` with a center `ℓ` and a radius base `r₀`.
--
--   * `START`: after `s` outer iterations, move to the next phase; else skip the iteration on a fair
--     bit, or go to `SAMPLE`.
--   * `SAMPLE`: sample a center `ℓ` of `LS \ R⁻`, with weight its local-search cluster cost (phase
--     `0`) or the cost of its cluster in the mixed set `(LS \ R⁻, Λ₁ ++ Λ₂)` (phase `1`).
--   * `RADD ℓ`: on a fair bit (and `|R⁻| ≤ s`) delete `ℓ` and end the iteration, else go to `DG ℓ`.
--   * `DG ℓ`: (unless `|Λ₂| + |R⁻| > 2s`) with `c'` the nearest other center, on a fair bit go to
--     `RG ℓ d(ℓ, c')`, else delete `c'` and stay.
--   * `RG ℓ r₀`: (unless `|Λ₂| + |R⁻| > 2s`) add the dummy `(ℓ, grid(r₀, x) + t r₀/(N⁴ (2s + 2)))`,
--     `x` uniform, `t = |Λ₂|`, go to `RGB ℓ r₀` (`BCFGJPSSV26.Stable.ksRad`).
--   * `RGB ℓ r₀`: on a fair bit delete `ℓ` and end the iteration, else go back to `RG ℓ r₀`.
--
--   The shift `t r₀/(N⁴ (2s + 2)) < r₀/N⁴` of the radius keeps the dummies of one leader distinct:
--   two grid points differ by at least `r₀/N⁴`. So the analysis matches every dummy with its own
--   cluster, also when two clusters are at the same distance from the leader; the shift costs at most
--   `15 ε⁴ per` in the radius.
--
--   The output is `LS' = LS \ R⁻` and `Λ₂` (`BCFGJPSSV26.Stable.ksLS'`).
--   **Termination** (`BCFGJPSSV26.Stable.ksRun_phase`): every run is done within `M₂ = 20 s + 20` steps,
--   whatever the chunks: the outer iterations, deletions and additions are bounded. The potential
--   `BCFGJPSSV26.Stable.KSSteps.pot` (remaining iterations, mode, twice the room `2 s + 1 - |Λ₂| -
--   |R⁻|` of the guarded additions and deletions) starts at `14 s + 4` and drops at every step.
--
--   **Contents.** The module is published as a whole: 33 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.ksRun_phase` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSampling`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/ClusterSampling.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coins
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.ClusterSampling` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Cluster sampling

[BCFGJPSSV26b, Algorithm 2] as a state machine reading one chunk per step
(`BCFGJPSSV26.Stable.ksStep`, `BCFGJPSSV26.Stable.ksRun`). The state
(`BCFGJPSSV26.Stable.KSState`) is the phase (`0`, `1`, or `2` when done), the outer counter `j`,
the deleted centers `R⁻`, the dummies `Λ₂`, and the mode: `START`, `SAMPLE`, `RADD ℓ`, `DG ℓ`,
`RG ℓ r₀`, `RGB ℓ r₀`, coded by a tag `0, …, 5` with a center `ℓ` and a radius base `r₀`.

* `START`: after `s` outer iterations, move to the next phase; else skip the iteration on a fair
  bit, or go to `SAMPLE`.
* `SAMPLE`: sample a center `ℓ` of `LS \ R⁻`, with weight its local-search cluster cost (phase
  `0`) or the cost of its cluster in the mixed set `(LS \ R⁻, Λ₁ ++ Λ₂)` (phase `1`).
* `RADD ℓ`: on a fair bit (and `|R⁻| ≤ s`) delete `ℓ` and end the iteration, else go to `DG ℓ`.
* `DG ℓ`: (unless `|Λ₂| + |R⁻| > 2s`) with `c'` the nearest other center, on a fair bit go to
  `RG ℓ d(ℓ, c')`, else delete `c'` and stay.
* `RG ℓ r₀`: (unless `|Λ₂| + |R⁻| > 2s`) add the dummy `(ℓ, grid(r₀, x) + t r₀/(N⁴ (2s + 2)))`,
  `x` uniform, `t = |Λ₂|`, go to `RGB ℓ r₀` (`BCFGJPSSV26.Stable.ksRad`).
* `RGB ℓ r₀`: on a fair bit delete `ℓ` and end the iteration, else go back to `RG ℓ r₀`.

The shift `t r₀/(N⁴ (2s + 2)) < r₀/N⁴` of the radius keeps the dummies of one leader distinct:
two grid points differ by at least `r₀/N⁴`. So the analysis matches every dummy with its own
cluster, also when two clusters are at the same distance from the leader; the shift costs at most
`15 ε⁴ per` in the radius.

The output is `LS' = LS \ R⁻` and `Λ₂` (`BCFGJPSSV26.Stable.ksLS'`).
**Termination** (`BCFGJPSSV26.Stable.ksRun_phase`): every run is done within `M₂ = 20 s + 20` steps,
whatever the chunks: the outer iterations, deletions and additions are bounded. The potential
`BCFGJPSSV26.Stable.KSSteps.pot` (remaining iterations, mode, twice the room `2 s + 1 - |Λ₂| -
|R⁻|` of the guarded additions and deletions) starts at `14 s + 4` and drops at every step.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

/-- The state of the cluster sampling: phase, outer counter, deleted centers, dummies, mode tag,
center `ℓ` and radius base `r₀` of the mode. -/
abbrev KSState : Type := ℕ × ℕ × List ℕ × List DumQ × ℕ × ℕ × ℚ

namespace KSState

/-- The phase: `0`, `1`, or `2` when done. -/
def phase (st : KSState) : ℕ := st.1

/-- The outer counter. -/
def j (st : KSState) : ℕ := st.2.1

/-- The deleted centers `R⁻`. -/
def del (st : KSState) : List ℕ := st.2.2.1

/-- The dummies `Λ₂`. -/
def dums (st : KSState) : List DumQ := st.2.2.2.1

/-- The mode tag: `0` START, `1` SAMPLE, `2` RADD, `3` DG, `4` RG, `5` RGB. -/
def tag (st : KSState) : ℕ := st.2.2.2.2.1

/-- The center of the mode. -/
def ldr (st : KSState) : ℕ := st.2.2.2.2.2.1

/-- The radius base of the mode. -/
def r₀ (st : KSState) : ℚ := st.2.2.2.2.2.2

@[simp] theorem phase_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.phase (a, b, c, d, e, f, g) = a := rfl
@[simp] theorem j_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.j (a, b, c, d, e, f, g) = b := rfl
@[simp] theorem del_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.del (a, b, c, d, e, f, g) = c := rfl
@[simp] theorem dums_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.dums (a, b, c, d, e, f, g) = d := rfl
@[simp] theorem tag_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.tag (a, b, c, d, e, f, g) = e := rfl
@[simp] theorem ldr_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.ldr (a, b, c, d, e, f, g) = f := rfl
@[simp] theorem r₀_mk (a b : ℕ) (c : List ℕ) (d : List DumQ) (e f : ℕ) (g : ℚ) :
    KSState.r₀ (a, b, c, d, e, f, g) = g := rfl

end KSState

/-- The initial state: phase `0`, `START`. -/
def ksInit : KSState := (0, 0, [], [], 0, 0, 0)

/-- The sampling weights of the candidates `cand`: their local-search cluster costs in phase `0`,
the costs `∑_{y ∈ M_c} d(y, c)` of their clusters in `(LS \ R⁻, Λ₁ ++ Λ₂)` in phase `1`. -/
def ksWeights (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (ph : ℕ) (del : List ℕ)
    (dums : List DumQ) (cand : List ℕ) : List ℚ :=
  if ph = 0 then cand.map fun c ↦ x.costOn LS (x.clusterQ LS c)
  else cand.map fun c ↦
    (((x.clusterMixQ (LS.filter fun c' ↦ decide (c' ∉ del)) (Λ₁ ++ dums) c).map
      fun y ↦ x.fdist y c).sum)

/-- The radius of the `t`-th dummy from the grid point `x` of base `r₀`:
`grid(r₀, x) + t r₀/(N⁴ (2s + 2))`. -/
def ksRad (N s : ℕ) (r₀ : ℚ) (x t : ℕ) : ℚ := grid N r₀ x + r₀ * t / ((N : ℚ) ^ 4 * (2 * s + 2))

/-- **One step of the cluster sampling**, reading the chunk `u`. -/
def ksStep (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ) (st : KSState)
    (u : ℕ) : KSState :=
  match st with
  | (ph, j, del, dums, tag, l, r₀) =>
    if ph = 2 then st
    else if tag = 0 then
      if j = s then (if ph = 0 then (1, 0, del, dums, 0, l, r₀) else (2, 0, del, dums, 0, l, r₀))
      else if cbit b u then (ph, j + 1, del, dums, 0, l, r₀)
      else (ph, j, del, dums, 1, l, r₀)
    else if tag = 1 then
      let cand := LS.filter fun c ↦ decide (c ∉ del)
      if cand = [] then (ph, j + 1, del, dums, 0, l, r₀)
      else (ph, j, del, dums, 2,
        cand.getD (wsample b (ksWeights x LS Λ₁ ph del dums cand) u) 0, r₀)
    else if tag = 2 then
      if del.length ≤ s ∧ cbit b u = true then (ph, j + 1, del ++ [l], dums, 0, l, r₀)
      else (ph, j, del, dums, 3, l, r₀)
    else if tag = 3 then
      if 2 * s < dums.length + del.length then (ph, j + 1, del, dums, 0, l, r₀)
      else
        let cand := LS.filter fun c ↦ decide (c ∉ del ∧ c ≠ l)
        if cand = [] then (ph, j + 1, del, dums, 0, l, r₀)
        else
          let c' := x.nearQ (x.n + l) cand
          if cbit b u then (ph, j, del, dums, 4, l, x.fdist (x.n + l) c')
          else (ph, j, del ++ [c'], dums, 3, l, r₀)
    else if tag = 4 then
      if 2 * s < dums.length + del.length then (ph, j + 1, del ++ [l], dums, 0, l, r₀)
      else (ph, j, del, dums ++ [(x.n + l, ksRad N s r₀ (cunif (Par.Gr N) u) dums.length)], 5,
        l, r₀)
    else
      if cbit b u then (ph, j + 1, del ++ [l], dums, 0, l, r₀)
      else (ph, j, del, dums, 4, l, r₀)

/-- **The cluster sampling**: `20 s + 20` steps from the initial state. -/
def ksRun (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ) (ch : ℕ → ℕ) : KSState :=
  (List.range (20 * s + 20)).foldl (fun st t ↦ ksStep N x LS Λ₁ s b st (ch t)) ksInit

/-- The centers kept: `LS \ R⁻`. -/
def ksLS' (LS : List ℕ) (st : KSState) : List ℕ := LS.filter fun c ↦ decide (c ∉ st.del)

/-! ### Termination: a potential argument -/

namespace KSSteps

/-- The steps left in the current outer iteration from a mode (`START` counts the iteration). -/
def modeCost (tag : ℕ) : ℕ :=
  if tag = 0 then 5 else if tag = 1 then 4 else if tag = 2 then 3 else if tag = 3 then 2
  else if tag = 4 then 1 else 2

/-- The potential: the remaining iterations, the mode, and twice the room `2 s + 1 - |Λ₂| - |R⁻|`
of the guarded additions and deletions. -/
def pot (s : ℕ) (st : KSState) : ℕ :=
  (if st.phase = 0 then 5 * s + 1 else 0) +
    (if st.tag = 0 then 5 * (s - st.j) + 1 else 5 * (s - st.j - 1) + 1 + modeCost st.tag) +
    2 * (2 * s + 1 - (st.dums.length + st.del.length))

/-- The counter is at most `s`, and below `s` inside an iteration. -/
def WF (s : ℕ) (st : KSState) : Prop := st.j ≤ s ∧ (st.tag ≠ 0 → st.j < s)

theorem step_phase_two (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (st : KSState) (u : ℕ) (h : st.phase = 2) : ksStep N x LS Λ₁ s b st u = st := by
  obtain ⟨ph, j, del, dums, tag, l, r₀⟩ := st
  simp only [KSState.phase_mk] at h
  subst h
  simp [ksStep]

theorem step_pot (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (st : KSState) (u : ℕ) (hw : WF s st) (h : st.phase ≠ 2) :
    (ksStep N x LS Λ₁ s b st u).phase = 2 ∨
      (WF s (ksStep N x LS Λ₁ s b st u) ∧
        pot s (ksStep N x LS Λ₁ s b st u) + 1 ≤ pot s st) := by
  obtain ⟨ph, j, del, dums, tag, l, r₀⟩ := st
  simp only [WF, KSState.phase_mk, KSState.j_mk, KSState.tag_mk] at hw h
  obtain ⟨hj, ht⟩ := hw
  unfold ksStep
  simp only [h, ite_false]
  by_cases hph : ph = 0 <;> split_ifs <;>
    simp_all [WF, pot, modeCost] <;> omega

theorem foldl_phase_two (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (us : List ℕ) (st : KSState) (h : st.phase = 2) :
    us.foldl (fun st u ↦ ksStep N x LS Λ₁ s b st u) st = st := by
  induction us with
  | nil => rfl
  | cons u us ih => rw [List.foldl_cons, step_phase_two N x LS Λ₁ s b st u h, ih]

theorem foldl_pot (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (us : List ℕ) (st : KSState) (hw : WF s st) :
    (us.foldl (fun st u ↦ ksStep N x LS Λ₁ s b st u) st).phase = 2 ∨
      pot s (us.foldl (fun st u ↦ ksStep N x LS Λ₁ s b st u) st) + us.length ≤ pot s st := by
  induction us generalizing st with
  | nil => exact .inr le_rfl
  | cons u us ih =>
    rw [List.foldl_cons, List.length_cons]
    by_cases h : st.phase = 2
    · rw [step_phase_two N x LS Λ₁ s b st u h, foldl_phase_two N x LS Λ₁ s b us st h]
      exact .inl h
    rcases step_pot N x LS Λ₁ s b st u hw h with h' | ⟨hw', hp⟩
    · rw [foldl_phase_two N x LS Λ₁ s b us _ h']
      exact .inl h'
    · rcases ih _ hw' with h'' | h''
      · exact .inl h''
      · exact .inr (by omega)

end KSSteps

/-! ### The leaders of the dummies -/

/-- The dummies are led by centers of `LS`, and so is the mode. -/
def LeadersIn (n : ℕ) (LS : List ℕ) (st : KSState) : Prop :=
  (∀ l ∈ st.dums, ∃ i ∈ LS, l.1 = n + i) ∧ (st.tag ≠ 0 → st.tag ≠ 1 → st.ldr ∈ LS)

theorem ksWeights_length (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (ph : ℕ) (del : List ℕ)
    (dums : List DumQ) (cand : List ℕ) : (ksWeights x LS Λ₁ ph del dums cand).length =
      cand.length := by
  unfold ksWeights
  split_ifs <;> simp

/-- The sampled center is a candidate. -/
theorem getD_wsample_mem (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (ph : ℕ) (del : List ℕ)
    (dums : List DumQ) {cand : List ℕ} (hc : cand ≠ []) (b u : ℕ) :
    cand.getD (wsample b (ksWeights x LS Λ₁ ph del dums cand) u) 0 ∈ cand := by
  have hw : ksWeights x LS Λ₁ ph del dums cand ≠ [] := by
    intro h
    have := ksWeights_length x LS Λ₁ ph del dums cand
    rw [h, List.length_nil] at this
    exact hc (List.length_eq_zero_iff.1 this.symm)
  have hlt := wsample_lt (b := b) hw u
  rw [ksWeights_length] at hlt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_mem hlt

theorem leadersIn_step (N : ℕ) (x : Raw) (LS : List ℕ) (Λ₁ : List DumQ) (s b : ℕ)
    (st : KSState) (u : ℕ) (h : LeadersIn x.n LS st) :
    LeadersIn x.n LS (ksStep N x LS Λ₁ s b st u) := by
  obtain ⟨ph, j, del, dums, tag, l, r₀⟩ := st
  simp only [LeadersIn, KSState.dums_mk, KSState.tag_mk, KSState.ldr_mk] at h
  obtain ⟨hd, hl⟩ := h
  have k0 : ∀ (a b : ℕ) (c : List ℕ) (f : ℕ) (g : ℚ),
      LeadersIn x.n LS (a, b, c, dums, 0, f, g) :=
    fun _ _ _ _ _ ↦ ⟨hd, fun h _ ↦ absurd rfl h⟩
  have k1 : ∀ (a b : ℕ) (c : List ℕ) (f : ℕ) (g : ℚ),
      LeadersIn x.n LS (a, b, c, dums, 1, f, g) :=
    fun _ _ _ _ _ ↦ ⟨hd, fun _ h ↦ absurd rfl h⟩
  have kl : ∀ (a b : ℕ) (c : List ℕ) (e : ℕ) (g : ℚ), tag ≠ 0 → tag ≠ 1 →
      LeadersIn x.n LS (a, b, c, dums, e, l, g) :=
    fun _ _ _ _ _ h0 h1 ↦ ⟨hd, fun _ _ ↦ hl h0 h1⟩
  have kr : tag ≠ 0 → tag ≠ 1 → ∀ (a b : ℕ) (c : List ℕ) (e : ℕ) (g r : ℚ),
      LeadersIn x.n LS (a, b, c, dums ++ [(x.n + l, r)], e, l, g) := by
    intro h0 h1 _ _ _ _ _ _
    refine ⟨fun d hd' ↦ ?_, fun _ _ ↦ hl h0 h1⟩
    rcases List.mem_append.1 hd' with hd' | hd'
    · exact hd d hd'
    · rw [List.mem_singleton.1 hd']
      exact ⟨l, hl h0 h1, rfl⟩
  dsimp only [ksStep]
  split_ifs <;> first
    | exact ⟨hd, hl⟩
    | exact k0 _ _ _ _ _
    | exact k1 _ _ _ _ _
    | exact kl _ _ _ _ _ ‹_› ‹_›
    | exact kr ‹_› ‹_› _ _ _ _ _ _
    | exact ⟨hd, fun _ _ ↦ List.mem_of_mem_filter (getD_wsample_mem x LS Λ₁ ph del dums ‹_› b u)⟩

/-- The dummies of the cluster sampling are led by the centers of `LS`. -/
theorem ksRun_dums {I : Instance} {LS : List ℕ} (hLS : ∀ i ∈ LS, i < I.m) (N : ℕ)
    (Λ₁ : List DumQ) (s b : ℕ) (ch : ℕ → ℕ) :
    ∀ l ∈ (ksRun N (toRaw I) LS Λ₁ s b ch).dums, ∃ i ∈ LS, l.1 = I.n + i := by
  have _ := hLS
  have key : ∀ (ts : List ℕ) (st : KSState), LeadersIn (toRaw I).n LS st →
      LeadersIn (toRaw I).n LS
        (ts.foldl (fun st t ↦ ksStep N (toRaw I) LS Λ₁ s b st (ch t)) st) := by
    intro ts
    induction ts with
    | nil => exact fun _ h ↦ h
    | cons t ts ih => exact fun st h ↦ ih _ (leadersIn_step N _ LS Λ₁ s b st _ h)
  exact (key _ ksInit ⟨fun _ h ↦ by simp [ksInit, KSState.dums] at h,
    fun h _ ↦ absurd rfl h⟩).1

end BCFGJPSSV26.Stable


