-- Prove2me | Definitions.Def_DistRobustHalfspace_Main_Algorithm1
-- name    : DistRobustHalfspace_Main_Algorithm1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:12.631895+00:00
-- url     : https://prove2.me/theorems/bfdf4eb5-ab10-4193-aa3b-fbdc38182466
-- title:
--   Algorithm 1 (the picky tester) with its subroutines and unspecified Θ(·) constants as parameters; the statistic Z
-- statement:
--   **Algorithm 1** (p. 26), with input dimension $n$ and proximity parameter $\varepsilon^*$, as a `Tester n Bool` (`alg1 P n ε∗`, `true` = Accept). Write $\varepsilon=\varepsilon^*/2$. The constants the paper leaves as "sufficiently large" are parameters $P$: $c_m,c_p,c_S$ (lines 1, 3, 5) and $L_{15},L_{19},L_{20},L_{21}$ (the constants $L$ in the proofs of Lemmas 2.15, 2.19, 2.20, 2.21). With these, $m=\lceil c_m n^{2/3}/\varepsilon^{10}\rceil$ (`alg1M`), $p=\lceil c_p/\varepsilon^{28}\rceil$ and $|S|=\lceil c_S/\varepsilon\rceil$.
--
--   1. **Line 2** (algorithm of Lemma 2.21, p. 23). Draw $\lceil L_{21}/\varepsilon^{12}\rceil$ samples from $D$ and query $f$ at each. Let $\hat p$ be the fraction labelled $-1$. If $\hat p\notin[\varepsilon/4,1-\varepsilon/4]$ the estimator outputs $\bot$ and the algorithm **accepts**; otherwise $\hat t=\Phi^{-1}(\hat p)$.
--   2. **Line 3.** Draw $N=(g_1,\dots,g_p)\sim\mathcal N(0,I_n)^p$.
--   3. **Line 4, test of Lemma 2.15** (p. 18, $K=1000$). Draw $X\sim\mathcal N(0,I_n)^{m'}$ with $m'=\lceil L_{15}m\rceil$ and query $f$ on $X$. For each of $Km'$ samples $y_i\sim D$, reject if $\|y_i\|>2\sqrt n$ or $|\hat G_{y_i}|>B/2$, where $\hat G_y=\frac1{m'}\sum_{x\in X}\langle y,xf(x)/\tau(\hat t)\rangle$.
--   4. **Line 4, test of Lemma 2.19** (p. 21). Draw $y_i,z_i\sim D$ for $i\le s=\lceil L_{19}\sqrt n\rceil$; reject if $\hat Q=s^{-2}\sum_{i,j}\langle y_i,z_j\rangle^2>2n$.
--   5. **Line 4, test of Lemma 2.20** (p. 22). Draw $s=\lceil L_{20}\sqrt nR_\varepsilon^2\rceil$ samples $y_i\sim D$; reject if $\|\hat\mu\|^2>2(\sqrt n+R_\varepsilon^2)$, where $\hat\mu=\frac1s\sum_i f(y_i)\hat\alpha_{f,N}(y_i)y_i$.
--   6. **Lines 5–6.** Draw $S$; reject if $|\{y\in S:\hat\alpha_{f,N}(y)<\varepsilon/4\}|/|S|>3\varepsilon/8$.
--   7. **Lines 7–10.** Draw $w_i,z_j\sim\mathcal N(0,I_n)$ and $y_k\sim D$ ($m$ each). Set $\hat w=\frac1{\tau(\hat t)}\frac1m\sum_i w_if(w_i)$ and $\hat z$ likewise, and
--   $$Z_1=\tfrac1m\textstyle\sum_k(\langle y_k,\hat w\rangle-\hat t)(\langle y_k,\hat z\rangle-\hat t),\quad Z_2=\tfrac1m\sum_kf(y_k)(\langle y_k,\hat w\rangle-\hat t)\hat\alpha_{f,N}(y_k),\quad Z_3=\tfrac1m\sum_k\hat\alpha_{f,N}(y_k)^2.$$
--   **Accept** iff $Z=Z_1-2Z_2+Z_3\le\varepsilon^3/64$.
--
--   Every query point is a function of the samples and the Gaussian points only, so the algorithm is non-adaptive. Each $\hat\alpha_{f,N}(y)$ costs the $p+1$ queries $f(y)$ and $f(y+g_j)$. `statZ ε t̂ f N w z y` is the statistic $Z$ of lines 8–10 for fixed $\hat t$ and $N$. `line7Law n m D` is the joint law of $(w,z,y)\sim\mathcal N(0,I_n)^m\otimes\mathcal N(0,I_n)^m\otimes D^m$. `P.AllAtLeast c` says every constant of $P$ is at least $c$.
--
--   **Formalization Note.** Algorithm 1 runs "the algorithms from Lemmas 2.15, 2.19 and 2.20" and "Lemma 2.21". These are the algorithms constructed in those lemmas' proofs, and they are written out here. Their unspecified constants are parameters, as are the $\Theta(\cdot)$ constants of Algorithm 1. The rejection tests are evaluated together, which is equivalent to running them in sequence, because the queries are non-adaptive.
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Algorithm 1, p. 26 (PDF 28), with the algorithms in the proofs of Lemma 2.15 (p. 18), Lemma 2.19 (p. 21), Lemma 2.20 (p. 22), Lemma 2.21 (p. 23)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- The constants that Algorithm 1 (p. 26) and the proofs of the subroutines it calls leave as
"sufficiently large" `Θ(·)` / `L` constants:
`cm` (line 1, `m = Θ(n^{2/3}/ε^{10})`), `cp` (line 3, `p = Θ(1/ε^{28})`),
`cS` (line 5, `|S| = Θ(1/ε)`), `L15` (proof of Lemma 2.15, `m′ = L m`),
`L19` (proof of Lemma 2.19, `s = L √n`), `L20` (proof of Lemma 2.20, `s = L √n R_ε²`),
`L21` (proof of Lemma 2.21, `s = L / ε^{12}`). -/
structure Alg1Consts where
  cm : ℝ
  cp : ℝ
  cS : ℝ
  L15 : ℝ
  L19 : ℝ
  L20 : ℝ
  L21 : ℝ

/-- Every constant of `P` is at least `c` ("sufficiently large constants"). -/
def Alg1Consts.AllAtLeast (P : Alg1Consts) (c : ℝ) : Prop :=
  c ≤ P.cm ∧ c ≤ P.cp ∧ c ≤ P.cS ∧ c ≤ P.L15 ∧ c ≤ P.L19 ∧ c ≤ P.L20 ∧ c ≤ P.L21

/-- `m = ⌈cm · n^{2/3} / ε^{10}⌉` (Algorithm 1, line 1). -/
noncomputable def alg1M (cm : ℝ) (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈cm * (n : ℝ) ^ ((2 : ℝ) / 3) / ε ^ 10⌉₊

/-- The test statistic `Z = Z₁ − 2Z₂ + Z₃` of Algorithm 1, lines 8–10, computed from the points
`w, z ∼ N(0, Iₙ)^m`, `y ∼ D^m`, the answers `f(wᵢ)`, `f(zⱼ)`, `f(y_k)` and the answers
`f(y_k + g_j)` used for `α̂_{f,N}(y_k)`:
`ŵ = (1/τ(t̂)) (1/m) Σ wᵢ f(wᵢ)`, `ẑ = (1/τ(t̂)) (1/m) Σ zⱼ f(zⱼ)`,
`Z₁ = (1/m) Σ_k (⟨y_k, ŵ⟩ − t̂)(⟨y_k, ẑ⟩ − t̂)`, `Z₂ = (1/m) Σ_k f(y_k)(⟨y_k, ŵ⟩ − t̂) α̂_{f,N}(y_k)`,
`Z₃ = (1/m) Σ_k α̂_{f,N}(y_k)²`. -/
noncomputable def statZcore {n : ℕ} (ε t : ℝ) (p m : ℕ) (w z y : Fin m → Rn n)
    (fw fz fy : Fin m → ℝ) (fyg : Fin m → Fin p → ℝ) : ℝ :=
  let τ := tau t
  let wh : Rn n := (τ⁻¹ * (1 / (m : ℝ))) • ∑ i, fw i • w i
  let zh : Rn n := (τ⁻¹ * (1 / (m : ℝ))) • ∑ j, fz j • z j
  let ah : Fin m → ℝ := fun k => alphaHatOf ε (fy k) (fyg k)
  let Z1 := (1 / (m : ℝ)) * ∑ k, (⟪y k, wh⟫ - t) * (⟪y k, zh⟫ - t)
  let Z2 := (1 / (m : ℝ)) * ∑ k, fy k * (⟪y k, wh⟫ - t) * ah k
  let Z3 := (1 / (m : ℝ)) * ∑ k, ah k ^ 2
  Z1 - 2 * Z2 + Z3

/-- The statistic `Z` of Algorithm 1 for a function `f`, threshold `t̂`, neighborhood tuple `N` and
the draws `w, z, y` of line 7 (with `m` points each). -/
noncomputable def statZ {n p m : ℕ} (ε t : ℝ) (f : Rn n → ℝ) (N : Fin p → Rn n)
    (w z y : Fin m → Rn n) : ℝ :=
  statZcore ε t p m w z y (fun i => f (w i)) (fun j => f (z j)) (fun k => f (y k))
    (fun k j => f (y k + N j))

/-- The law of `(w, z, y)` in line 7 of Algorithm 1: `w, z ∼ N(0, Iₙ)^m` and `y ∼ D^m`,
independent. -/
noncomputable def line7Law (n m : ℕ) (D : ProbabilityMeasure (Rn n)) :
    Measure ((Fin m → Rn n) × (Fin m → Rn n) × (Fin m → Rn n)) :=
  (Measure.pi fun _ : Fin m => stdGaussian (Rn n)).prod
    ((Measure.pi fun _ : Fin m => stdGaussian (Rn n)).prod
      (Measure.pi fun _ : Fin m => (D : Measure (Rn n))))

namespace Alg1

/-- `m` of line 1 (with `ε` the halved proximity parameter). -/
noncomputable def m (P : Alg1Consts) (n : ℕ) (ε : ℝ) : ℕ := alg1M P.cm n ε
/-- `p` of line 3. -/
noncomputable def p (P : Alg1Consts) (ε : ℝ) : ℕ := ⌈P.cp / ε ^ 28⌉₊
/-- `|S|` of line 5. -/
noncomputable def sS (P : Alg1Consts) (ε : ℝ) : ℕ := ⌈P.cS / ε⌉₊
/-- `m′ = L m` (proof of Lemma 2.15). -/
noncomputable def m' (P : Alg1Consts) (n : ℕ) (ε : ℝ) : ℕ := ⌈P.L15 * (m P n ε : ℝ)⌉₊
/-- `K m′` samples of the test of Lemma 2.15, with `K = 1000` (line 4). -/
noncomputable def k15 (P : Alg1Consts) (n : ℕ) (ε : ℝ) : ℕ := 1000 * m' P n ε
/-- `s = L √n` (proof of Lemma 2.19). -/
noncomputable def s19 (P : Alg1Consts) (n : ℕ) : ℕ := ⌈P.L19 * Real.sqrt n⌉₊
/-- `s = L √n R_ε²` (proof of Lemma 2.20). -/
noncomputable def s20 (P : Alg1Consts) (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈P.L20 * Real.sqrt n * Reps ε ^ 2⌉₊
/-- `s = L / ε^{12}` (proof of Lemma 2.21). -/
noncomputable def s21 (P : Alg1Consts) (ε : ℝ) : ℕ := ⌈P.L21 / ε ^ 12⌉₊

/-- Samples from `D`: line 2 (Lemma 2.21), line 4 (Lemma 2.15; Lemma 2.19's `y`'s and `z`'s;
Lemma 2.20), line 5 (`S`), line 7 (`y₁, …, y_m`). -/
abbrev SampleIdx (P : Alg1Consts) (n : ℕ) (ε : ℝ) : Type :=
  Fin (s21 P ε) ⊕ Fin (k15 P n ε) ⊕ (Fin (s19 P n) ⊕ Fin (s19 P n)) ⊕ Fin (s20 P n ε) ⊕
    Fin (sS P ε) ⊕ Fin (m P n ε)

/-- Internal Gaussian points: the neighborhood tuple `N` (line 3), Lemma 2.15's `X` (line 4), and
`w₁, …, w_m`, `z₁, …, z_m` (line 7). -/
abbrev GaussIdx (P : Alg1Consts) (n : ℕ) (ε : ℝ) : Type :=
  Fin (p P ε) ⊕ Fin (m' P n ε) ⊕ Fin (m P n ε) ⊕ Fin (m P n ε)

/-- Queries: line 2 (at its samples), Lemma 2.15 (at `X`), Lemma 2.20 / line 5 / line 9 (at `y` and
at `y + gⱼ`, `p + 1` queries per point), line 8 (at the `wᵢ` and `zⱼ`). -/
abbrev QueryIdx (P : Alg1Consts) (n : ℕ) (ε : ℝ) : Type :=
  Fin (s21 P ε) ⊕ Fin (m' P n ε) ⊕ (Fin (s20 P n ε) × Option (Fin (p P ε))) ⊕
    (Fin (sS P ε) × Option (Fin (p P ε))) ⊕ Fin (m P n ε) ⊕ Fin (m P n ε) ⊕
    (Fin (m P n ε) × Option (Fin (p P ε)))

/-- The point `y` (`none`) or `y + gⱼ` (`some j`). -/
def nbr {n p : ℕ} (y : Rn n) (N : Fin p → Rn n) : Option (Fin p) → Rn n
  | none => y
  | some j => y + N j

/-- The query points of Algorithm 1, a function of the samples and the Gaussian points only. -/
noncomputable def query (P : Alg1Consts) (n : ℕ) (ε : ℝ) (S : SampleIdx P n ε → Rn n)
    (ω : GaussIdx P n ε → Rn n) : QueryIdx P n ε → Rn n
  | .inl i => S (.inl i)
  | .inr (.inl j) => ω (.inr (.inl j))
  | .inr (.inr (.inl (i, o))) => nbr (S (.inr (.inr (.inr (.inl i))))) (fun j => ω (.inl j)) o
  | .inr (.inr (.inr (.inl (i, o)))) =>
      nbr (S (.inr (.inr (.inr (.inr (.inl i)))))) (fun j => ω (.inl j)) o
  | .inr (.inr (.inr (.inr (.inl i)))) => ω (.inr (.inr (.inl i)))
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => ω (.inr (.inr (.inr j)))
  | .inr (.inr (.inr (.inr (.inr (.inr (k, o)))))) =>
      nbr (S (.inr (.inr (.inr (.inr (.inr k)))))) (fun j => ω (.inl j)) o

open Classical in
/-- The decision of Algorithm 1 (`true` = Accept), from the samples `S`, the Gaussian points `ω`
and the answers `a`, with `ε` the halved proximity parameter:
* line 2 (Lemma 2.21's estimator): `p̂` = fraction of the line-2 samples labelled `−1`; if
  `p̂ ∉ [ε/4, 1 − ε/4]` the estimator outputs `⊥` and the algorithm accepts; otherwise
  `t̂ = Φ⁻¹(p̂)`;
* line 4: Lemma 2.15's test (reject if some `‖yᵢ‖ > 2√n` or `|Ĝ_{yᵢ}| > B/2`, where
  `Ĝ_y = (1/m′) Σ_{x∈X} ⟨y, x f(x)/τ(t̂)⟩`), Lemma 2.19's test (reject if
  `Q̂ = s⁻² Σᵢⱼ ⟨yᵢ, zⱼ⟩² > 2n`), Lemma 2.20's test (reject if
  `‖μ̂‖² > 2(√n + R_ε²)`, `μ̂ = (1/s) Σ f(yᵢ) α̂_{f,N}(yᵢ) yᵢ`);
* line 6: reject if `|{y ∈ S : α̂_{f,N}(y) < ε/4}| / |S| > 3ε/8`;
* line 10: accept iff `Z ≤ ε³/64`. -/
noncomputable def decision (P : Alg1Consts) (n : ℕ) (ε : ℝ) (S : SampleIdx P n ε → Rn n)
    (ω : GaussIdx P n ε → Rn n) (a : QueryIdx P n ε → ℝ) : Bool :=
  let ph : ℝ := ((Finset.univ.filter fun i : Fin (s21 P ε) => a (.inl i) = -1).card : ℝ) /
    (s21 P ε : ℝ)
  let t : ℝ := Cohen2019.Robust.PhiInvReal ph
  let τ : ℝ := tau t
  -- Lemma 2.15's test
  let y15 : Fin (k15 P n ε) → Rn n := fun i => S (.inr (.inl i))
  let Gh : Rn n → ℝ := fun y => (1 / (m' P n ε : ℝ)) *
    ∑ j : Fin (m' P n ε), ⟪y, (a (.inr (.inl j)) / τ) • ω (.inr (.inl j))⟫
  let pass15 : Prop := ∀ i, ‖y15 i‖ ≤ 2 * Real.sqrt n ∧ |Gh (y15 i)| ≤ Bne n ε / 2
  -- Lemma 2.19's test
  let y19 : Fin (s19 P n) → Rn n := fun i => S (.inr (.inr (.inl (.inl i))))
  let z19 : Fin (s19 P n) → Rn n := fun j => S (.inr (.inr (.inl (.inr j))))
  let Qh : ℝ := (1 / (s19 P n : ℝ) ^ 2) * ∑ i, ∑ j, ⟪y19 i, z19 j⟫ ^ 2
  let pass19 : Prop := Qh ≤ 2 * n
  -- Lemma 2.20's test
  let y20 : Fin (s20 P n ε) → Rn n := fun i => S (.inr (.inr (.inr (.inl i))))
  let f20 : Fin (s20 P n ε) → ℝ := fun i => a (.inr (.inr (.inl (i, none))))
  let a20 : Fin (s20 P n ε) → ℝ := fun i =>
    alphaHatOf ε (f20 i) (fun j => a (.inr (.inr (.inl (i, some j)))))
  let μh : Rn n := (1 / (s20 P n ε : ℝ)) • ∑ i, (f20 i * a20 i) • y20 i
  let pass20 : Prop := ‖μh‖ ^ 2 ≤ 2 * (Real.sqrt n + Reps ε ^ 2)
  -- lines 5–6
  let aS : Fin (sS P ε) → ℝ := fun i =>
    alphaHatOf ε (a (.inr (.inr (.inr (.inl (i, none))))))
      (fun j => a (.inr (.inr (.inr (.inl (i, some j))))))
  let pass6 : Prop :=
    ((Finset.univ.filter fun i => aS i < ε / 4).card : ℝ) / (sS P ε : ℝ) ≤ 3 * ε / 8
  -- lines 7–10
  let w : Fin (m P n ε) → Rn n := fun i => ω (.inr (.inr (.inl i)))
  let z : Fin (m P n ε) → Rn n := fun j => ω (.inr (.inr (.inr j)))
  let y : Fin (m P n ε) → Rn n := fun k => S (.inr (.inr (.inr (.inr (.inr k)))))
  let Z : ℝ := statZcore ε t (p P ε) (m P n ε) w z y
    (fun i => a (.inr (.inr (.inr (.inr (.inl i))))))
    (fun j => a (.inr (.inr (.inr (.inr (.inr (.inl j)))))))
    (fun k => a (.inr (.inr (.inr (.inr (.inr (.inr (k, none))))))))
    (fun k j => a (.inr (.inr (.inr (.inr (.inr (.inr (k, some j))))))))
  Decidable.decide (¬ (ε / 4 ≤ ph ∧ ph ≤ 1 - ε / 4) ∨
    (pass15 ∧ pass19 ∧ pass20 ∧ pass6 ∧ Z ≤ ε ^ 3 / 64))

end Alg1

/-- **Algorithm 1** (p. 26) with input dimension `n` and proximity parameter `ε∗`, as a tester:
it works with `ε := ε∗/2`, draws its samples from `D`, draws the Gaussian points `N`, `X`, `w`,
`z` itself (internal randomness, i.i.d. `N(0, Iₙ)`), and queries `f` non-adaptively. Its output
is `true` (Accept) or `false` (Reject). The `Θ(·)`/`L` constants are the parameters `P`. -/
noncomputable def alg1 (P : Alg1Consts) (n : ℕ) (εstar : ℝ) : Tester n Bool where
  SampleIdx := Alg1.SampleIdx P n (εstar / 2)
  QueryIdx := Alg1.QueryIdx P n (εstar / 2)
  Ω := Alg1.GaussIdx P n (εstar / 2) → Rn n
  μ := Measure.pi fun _ => stdGaussian (Rn n)
  query := Alg1.query P n (εstar / 2)
  decide := Alg1.decision P n (εstar / 2)

end DistRobustHalfspace.Main


