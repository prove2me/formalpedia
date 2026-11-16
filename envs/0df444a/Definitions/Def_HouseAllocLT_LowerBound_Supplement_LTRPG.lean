-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_Supplement_LTRPG
-- name    : HouseAllocLT_LowerBound_Supplement_LTRPG
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:14:46.714793+00:00
-- url     : https://prove2.me/theorems/ac60c03b-5ff5-4438-bda3-f1457e8b52a8
-- title:
--   The constants (9), the reservation mechanism RES (14), LT-RPG and exact sampling
-- statement:
--   For $n\ge1$ the constants of (9) are
--   $$d_n=\sum_{j=0}^n(-1)^j\frac{n!}{j!},\qquad D_n=(n+2)!,\qquad \lambda_n=1-\frac{d_n}{n!}+\frac{\mathbf 1\{n\text{ even}\}}{n\,n!},$$
--   with reservation probability $\varepsilon_n=1/(100D_n)$ and $U_n=100D_n/((100D_n-1)\lambda_n)$.
--
--   The **reservation mechanism** RES (14) chooses one agent $d$ uniformly; conditional on $d$, it returns $\{(d,a)\}$ with probability
--   $$q_j(|C_j^d|)=\frac{4^{-j}}{m+|C_j^d|}$$
--   for every reported $a\in C_j^d$, and the empty matching with the remaining probability. For $\varepsilon\in[0,1]$ independent of the reports, $\mathrm{LT\text{-}RPG}_\varepsilon=(1-\varepsilon)\mathrm{RPG}+\varepsilon\,\mathrm{RES}$, and LT-RPG uses $\varepsilon_n$ on an $n$-agent market (Algorithm 2).
--
--   **Exact sampling in expected polynomial time** is formalized in Las Vegas form: one polynomial-time machine reads the code of the profile and polynomially many fair coins and either fails or outputs a matching; the success probability $\sigma(P)$ satisfies $1/\sigma(P)\le q(|\text{code}|)$ for a fixed polynomial $q$, and each matching $\mu$ is output with probability exactly $\sigma(P)\cdot\phi(P)(\mu)$. A routine family is polynomial-time if one polynomial-time machine computes it on coded edge sets.
--
--   **Formalization Note.** Classes are 0-based, so the class of index $k$ gets the factor $4^{-(k+1)}$. Profiles are coded with $n$, $m$ and list lengths in unary and each class as $m$ membership bits; edge sets as $nm$ membership bits. Polynomial time is the published `PolyTimeComputable` (Mathlib's multi-stack Turing machines).
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), display (9), PDF p. 10 (printed p. 8); display (14), PDF p. 13 (printed p. 11); Algorithm 2 and proof of Theorem 4.1, PDF p. 14 (printed p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_Supplement_RPG
import Definitions.Def_QAlgorithms_ClassicalStringComputability

open scoped BigOperators
open Classical

namespace HouseAllocLT.LowerBound.Supplement
open HouseAllocLT.LowerBound

noncomputable section

/-! # The constants (9), the reservation mechanism (14), LT-RPG (Algorithm 2), and exact sampling

Zhang, Zhao, Xu, Xi, Zhao, STOC 2027 submission #174 (October 2026), §4, PDF p. 10 (printed
p. 8), display (9); §4.6, PDF p. 13 (printed p. 11), display (14); Algorithm 2, PDF p. 14
(printed p. 12). -/

/-! ## The constants of (9) -/

/-- `d_n = Σ_{j=0}^{n} (−1)^j n!/j!` (each `n!/j!` an exact integer quotient). -/
def derangeNum (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * ((n.factorial / j.factorial : ℕ) : ℤ)

/-- `D_n = (n + 2)!` of (9). (Not the prefix-list domain `D_n` of §3.) -/
def resDenom (n : ℕ) : ℕ := (n + 2).factorial

/-- `λ_n = 1 − d_n/n! + 1{n even}/(n · n!)` of (9). -/
def lambdaN (n : ℕ) : ℝ :=
  1 - (derangeNum n : ℝ) / (n.factorial : ℝ) +
    (if Even n then 1 / ((n : ℝ) * (n.factorial : ℝ)) else 0)

/-- The reservation probability `ε_n = 1/(100 D_n)`. -/
def resProb (n : ℕ) : ℝ := 1 / (100 * (resDenom n : ℝ))

/-- `U_n = 100 D_n / ((100 D_n − 1) λ_n)` of (10). -/
def upperFactor (n : ℕ) : ℝ :=
  100 * (resDenom n : ℝ) / ((100 * (resDenom n : ℝ) - 1) * lambdaN n)

theorem resProb_mem_unitInterval (n : ℕ) : resProb n ∈ unitInterval := by
  have hD : (1 : ℝ) ≤ (resDenom n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  constructor
  · unfold resProb; positivity
  · unfold resProb
    rw [div_le_one (by positivity)]
    linarith

/-- `ε_n` as an element of `[0, 1]`. -/
def resProbI (n : ℕ) : unitInterval := ⟨resProb n, resProb_mem_unitInterval n⟩

/-! ## The reservation mechanism RES (14) -/

variable {n m : ℕ}

/-- The (0-based) index of the reported class containing `a` (`0` if `a` is unlisted). -/
def classIndex (p : Preference m) (a : Fin m) : ℕ :=
  if h : ∃ j, a ∈ p.classes j then Nat.find h else 0

/-- `q_j(|C_j^d|) = 4^{−j}/(m + |C_j^d|)` for a reported object `a ∈ C_j^d` (paper's 1-based
`j`; with the 0-based index `k` the factor is `4^{−(k+1)}`), and `0` for an unlisted object. -/
def resWeight (P : Profile n m) (d : Fin n) (a : Fin m) : ℝ :=
  if Acceptable (P d) a then
    (1 / 4 : ℝ) ^ (classIndex (P d) a + 1) /
      ((m : ℝ) + (((P d).classes (classIndex (P d) a)).card : ℝ))
  else 0

theorem resWeight_nonneg (P : Profile n m) (d : Fin n) (a : Fin m) : 0 ≤ resWeight P d a := by
  unfold resWeight; split_ifs <;> positivity

theorem resWeight_le (P : Profile n m) (d : Fin n) (a : Fin m) :
    resWeight P d a ≤ 1 / (m : ℝ) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast a.pos
  unfold resWeight
  split_ifs
  · have hc : (0 : ℝ) ≤ (((P d).classes (classIndex (P d) a)).card : ℝ) := by positivity
    have hp : (1 / 4 : ℝ) ^ (classIndex (P d) a + 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    calc (1 / 4 : ℝ) ^ (classIndex (P d) a + 1) /
          ((m : ℝ) + (((P d).classes (classIndex (P d) a)).card : ℝ))
        ≤ 1 / ((m : ℝ) + (((P d).classes (classIndex (P d) a)).card : ℝ)) :=
          div_le_div_of_nonneg_right hp (by positivity)
      _ ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm (by linarith)
  · positivity

/-- The total probability of a nonempty RES outcome: `Σ_d (1/n) Σ_a q(a)`. -/
def resTotal (P : Profile n m) : ℝ := ∑ d : Fin n, ∑ a : Fin m, resWeight P d a / (n : ℝ)

theorem resTotal_le_one (P : Profile n m) : resTotal P ≤ 1 := by
  unfold resTotal
  have h1 : ∀ d : Fin n, ∑ a : Fin m, resWeight P d a / (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro d
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc ∑ a : Fin m, resWeight P d a ≤ ∑ _a : Fin m, 1 / (m : ℝ) :=
          Finset.sum_le_sum (fun a _ => resWeight_le P d a)
      _ = (m : ℝ) * (1 / (m : ℝ)) := by simp
      _ ≤ 1 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · simp [h]
          · have : (0 : ℝ) < m := by exact_mod_cast h
            rw [mul_one_div_cancel this.ne']
  calc ∑ d : Fin n, ∑ a : Fin m, resWeight P d a / (n : ℝ) ≤ ∑ _d : Fin n, 1 / (n : ℝ) :=
        Finset.sum_le_sum (fun d _ => h1 d)
    _ = (n : ℝ) * (1 / (n : ℝ)) := by simp
    _ ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · have : (0 : ℝ) < n := by exact_mod_cast h
          rw [mul_one_div_cancel this.ne']

theorem feasible_singleton (P : Profile n m) (d : Fin n) (a : Fin m)
    (h : Acceptable (P d) a) : Feasible P {(d, a)} := by
  unfold Feasible TwoStageMatch.IsMatching
  simp [h]

/-- RES (14): choose `d` uniformly from the `n` agents; conditional on `d`, return `{(d, a)}` with
probability `q_j(|C_j^d|)` for each reported `a ∈ C_j^d`, and `∅` with the remaining probability. -/
def res : Mechanism n m where
  prob P μ :=
    (if μ = ∅ then 1 - resTotal P else 0) +
      ∑ d : Fin n, ∑ a : Fin m, if μ = {(d, a)} then resWeight P d a / (n : ℝ) else 0
  nonneg P μ := by
    apply add_nonneg
    · split_ifs
      · linarith [resTotal_le_one P]
      · exact le_refl 0
    · apply Finset.sum_nonneg; intro d _
      apply Finset.sum_nonneg; intro a _
      split_ifs
      · exact div_nonneg (resWeight_nonneg P d a) (by positivity)
      · exact le_refl 0
  total P := by
    rw [Finset.sum_add_distrib]
    have h2 : ∑ μ : Assignment n m, ∑ d : Fin n, ∑ a : Fin m,
        (if μ = {(d, a)} then resWeight P d a / (n : ℝ) else 0) = resTotal P := by
      rw [Finset.sum_comm]
      unfold resTotal
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp
    rw [h2]
    simp
  supported P μ h := by
    by_cases h0 : μ = ∅
    · rw [h0]; exact feasible_empty P
    · have hs : ∑ d : Fin n, ∑ a : Fin m,
          (if μ = {(d, a)} then resWeight P d a / (n : ℝ) else 0) ≠ 0 := by
        intro hz; apply h; simp [h0, hz]
      obtain ⟨d, _, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
      obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
      by_cases hμ : μ = {(d, a)}
      · rw [hμ]
        apply feasible_singleton
        by_contra hacc
        apply ha
        simp [hμ, resWeight, hacc]
      · exact absurd (by simp [hμ]) ha

/-! ## Mixtures and LT-RPG -/

/-- The mixture `(1 − ε) φ + ε ψ`: run `ψ` with probability `ε` and `φ` otherwise, the choice
independent of the reports. -/
def mix (ε : unitInterval) (φ ψ : Mechanism n m) : Mechanism n m where
  prob P μ := (1 - (ε : ℝ)) * φ.prob P μ + (ε : ℝ) * ψ.prob P μ
  nonneg P μ := by
    have h0 := ε.2.1
    have h1 := ε.2.2
    exact add_nonneg (mul_nonneg (by linarith) (φ.nonneg P μ)) (mul_nonneg h0 (ψ.nonneg P μ))
  total P := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, φ.total, ψ.total]
    ring
  supported P μ h := by
    by_cases hφ : φ.prob P μ = 0
    · have hψ : ψ.prob P μ ≠ 0 := by
        intro h2; apply h; simp [hφ, h2]
      exact ψ.supported P μ hψ
    · exact φ.supported P μ hφ

/-- `LT-RPG_ε = (1 − ε) RPG + ε RES` for a constant `ε ∈ [0, 1]` and the fixed routine `MM`. -/
def ltrpgEps (MM : MaxMatchingRoutine n m) (ε : unitInterval) : Mechanism n m :=
  mix ε (rpg MM) res

/-- LT-RPG on an `n`-agent market (Algorithm 2): `LT-RPG_{ε_n}` with `ε_n = 1/(100 (n + 2)!)`. -/
def ltrpg (MM : MaxMatchingRoutine n m) : Mechanism n m :=
  ltrpgEps MM (resProbI n)

/-- LT-RPG across all market sizes, using `ε_n` on an `n`-agent market and the routine `MMs n m`
on an `n`-agent, `m`-object market. -/
def ltrpgFamily (MMs : ∀ n m : ℕ, MaxMatchingRoutine n m) : MechanismFamily :=
  fun n m => ltrpg (MMs n m)

/-! ## Encodings and exact sampling in expected polynomial time -/

open QAlgorithms.Complexity

/-- A set of edges (in particular a matching) as the `n · m` membership bits, agent-major. -/
def encAssign (μ : Assignment n m) : Str :=
  (List.finRange n).flatMap (fun i => (List.finRange m).map (fun a => decide ((i, a) ∈ μ)))

/-- A class as its `m` membership bits. -/
def encClass (C : Finset (Fin m)) : Str :=
  (List.finRange m).map (fun a => decide (a ∈ C))

/-- A profile: `n` and `m` in unary, then for each agent its list length in unary and the
membership bits of each of its classes. The length lies between `n + m` and a polynomial in
`n, m`. -/
def encProfile (P : Profile n m) : Str :=
  encNat n ++ encNat m ++
    (List.finRange n).flatMap (fun i =>
      encNat (P i).length ++ (List.range (P i).length).flatMap (fun j => encClass ((P i).classes j)))

/-- A family of maximum-matching routines is polynomial-time computable: one polynomial-time
machine maps `n`, `m` (unary) and an edge set to the routine's matching. -/
def RoutinePolyTime (MMs : ∀ n m : ℕ, MaxMatchingRoutine n m) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧
    ∀ (n m : ℕ) (F : Assignment n m),
      g (encNat n ++ encNat m ++ encAssign F) = encAssign ((MMs n m).mm F)

/-- **Exact sampling in expected polynomial time** (Las Vegas form, with fair coins).
There are polynomials `c, q` and one polynomial-time machine `trial` such that, for every
`n, m ≥ 1` and every profile `P` with code `x = encProfile P`: a trial reads `x` followed by
`c(|x|)` fair coins and either succeeds, outputting `true` followed by the code of a matching, or
fails (any other output); the success probability `σ(P)` is positive with `1/σ(P) ≤ q(|x|)`; and
for every matching `μ`, the probability of outputting `μ` equals `σ(P) · φ(P)(μ)`, so that
conditional on success the output has law exactly `φ(P)`. Repeating independent trials until
success therefore samples `φ(P)` exactly with expected number of trials at most `q(|x|)`, each
trial in polynomial time. -/
def IsExactLasVegasSampler (φ : MechanismFamily) : Prop :=
  ∃ (c q : Polynomial ℕ) (trial : Str → Str), PolyTimeComputable trial ∧
    ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → ∀ P : Profile n m,
      let x := encProfile P
      let k := c.eval x.length
      let σ : ℝ := ((Finset.univ.filter (fun s : Fin k → Bool =>
          ∃ μ : Assignment n m, trial (x ++ List.ofFn s) = true :: encAssign μ)).card : ℝ) / 2 ^ k
      0 < σ ∧ 1 ≤ σ * ((q.eval x.length : ℕ) : ℝ) ∧
        ∀ μ : Assignment n m,
          ((Finset.univ.filter (fun s : Fin k → Bool =>
              trial (x ++ List.ofFn s) = true :: encAssign μ)).card : ℝ) / 2 ^ k =
            σ * (φ n m).prob P μ

end

end HouseAllocLT.LowerBound.Supplement


