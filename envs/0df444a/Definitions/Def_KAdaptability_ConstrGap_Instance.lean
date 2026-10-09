-- Prove2me | Definitions.Def_KAdaptability_ConstrGap_Instance
-- name    : KAdaptability_ConstrGap_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:00:54.076169+00:00
-- url     : https://prove2.me/theorems/2a713d25-ae72-467d-a2c6-7eb6535bc727
-- title:
--   The instance (EC.4) of 𝒫 from the proof of Theorem 4, with 𝒴 = {0,1}^Q
-- statement:
--   For $Q\in\mathbb N$, the instance (EC.4) of $\mathcal P$ from the proof of Theorem 4 (p. ec5) has no first-stage decision, second-stage feasible set $\mathcal Y=\{0,1\}^Q$, objective identically $0$, and the second-stage constraints
--   $$y_q-\xi_q\le \tfrac12,\qquad \xi_q-y_q\le\tfrac12,\qquad q=1,\dots,Q,$$
--   over the uncertainty set $[0,1]^Q$. Written as $\mathcal P$:
--   $$\max_{\xi\in[0,1]^Q}\ \min_{y\in\{0,1\}^Q}\{0 : y_q-\xi_q\le\tfrac12,\ \xi_q-y_q\le\tfrac12,\ q=1,\dots,Q\}.$$
--
--   The right-hand sides $\xi_q+\tfrac12$ and $-\xi_q+\tfrac12$ are affine in $\xi$. Following p. 6, an auxiliary parameter $\xi_{Q+1}$ is introduced and the uncertainty set is augmented with $\xi_{Q+1}=1$. Concretely, with $N=0$, $L=2Q$, parameter dimension $Q+1$ and $R=2Q+2$:
--
--   1. $C=0$, $Q=0$ (the matrix), $T=0$, $\mathcal X=\mathbb R^0$ (a single point);
--   2. $W=\begin{pmatrix}I\\-I\end{pmatrix}$ and $H=\begin{pmatrix}I & \tfrac12 e\\ -I & \tfrac12 e\end{pmatrix}$, so $Wy\le H\xi$ reads $y_q\le\xi_q+\tfrac12\xi_{Q+1}$ and $-y_q\le-\xi_q+\tfrac12\xi_{Q+1}$;
--   3. $\Xi$ is cut out by $\xi_q\le1$, $-\xi_q\le0$ ($q=1,\dots,Q$), $\xi_{Q+1}\le1$, $-\xi_{Q+1}\le-1$, i.e. $\Xi=[0,1]^Q\times\{1\}$.
--
--   The file also records three elementary facts used to build the instance: every point of $\{0,1\}^Q$ is a 0/1 vector, $|\{0,1\}^Q|=2^Q$, and $\Xi=[0,1]^Q\times\{1\}$ (which gives nonemptiness and boundedness).
--
--   **Formalization Note** $\{0,1\}^Q$ is the image of $\{\text{true},\text{false}\}^Q$ under $\beta\mapsto(\mathbb 1[\beta_q])_q$, as a `Finset (Fin Q → ℝ)`. The augmented coordinate $\xi_{Q+1}$ is `Fin.last Q`; the original coordinates are `Fin.castSucc q`. $Q=0$ is allowed.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec5 (PDF p. 39), Proof of Theorem 4, problem (EC.4); p. 6, affine dependence via ξ_{Q+1} = 1

import Mathlib
import Definitions.Def_KAdaptability_ConstrGap_Problem

open Matrix

namespace KAdaptability.ConstrGap

/-- The binary vector `y ∈ {0,1}^Q` encoded by `β : Fin Q → Bool` (`y_q = 1` iff `β q`). -/
def boolVec {nQ : ℕ} (β : Fin nQ → Bool) : Fin nQ → ℝ :=
  fun q => if β q then 1 else 0

/-- The set `{0,1}^Q ⊆ ℝ^Q` of all binary vectors, as a `Finset`. -/
noncomputable def binaryCube (nQ : ℕ) : Finset (Fin nQ → ℝ) :=
  Finset.univ.image (boolVec (nQ := nQ))

/-- Recourse matrix of (EC.4): `W = [I; −I] ∈ ℝ^{2Q×Q}`. Row `q` of the first block reads `y_q`,
row `q` of the second block reads `−y_q`. -/
def ec4W (nQ : ℕ) : Matrix (Fin (nQ + nQ)) (Fin nQ) ℝ :=
  Matrix.of fun l j =>
    Fin.addCases (fun q => if j = q then (1 : ℝ) else 0)
      (fun q => if j = q then (-1 : ℝ) else 0) l

/-- Right-hand side matrix of (EC.4) on the augmented parameter `(ξ_1, …, ξ_Q, ξ_{Q+1})`:
`H = [I, ½e; −I, ½e] ∈ ℝ^{2Q×(Q+1)}`, so that `(Hξ)_q = ξ_q + ½ ξ_{Q+1}` in the first block and
`−ξ_q + ½ ξ_{Q+1}` in the second. With `ξ_{Q+1} = 1`, the rows `Wy ≤ Hξ` are
`y_q − ξ_q ≤ 1/2` and `ξ_q − y_q ≤ 1/2`. -/
noncomputable def ec4H (nQ : ℕ) : Matrix (Fin (nQ + nQ)) (Fin (nQ + 1)) ℝ :=
  Matrix.of fun l i =>
    Fin.addCases
      (fun q => if i = Fin.castSucc q then (1 : ℝ) else if i = Fin.last nQ then 1 / 2 else 0)
      (fun q => if i = Fin.castSucc q then (-1 : ℝ) else if i = Fin.last nQ then 1 / 2 else 0) l

/-- Uncertainty set description of (EC.4), augmented by `ξ_{Q+1} = 1` (p. 6): rows
`ξ_q ≤ 1`, `−ξ_q ≤ 0` (`q = 1, …, Q`), `ξ_{Q+1} ≤ 1`, `−ξ_{Q+1} ≤ −1`. -/
def ec4A (nQ : ℕ) : Matrix (Fin ((nQ + nQ) + 2)) (Fin (nQ + 1)) ℝ :=
  Matrix.of fun r i =>
    Fin.addCases
      (Fin.addCases (fun q => if i = Fin.castSucc q then (1 : ℝ) else 0)
        (fun q => if i = Fin.castSucc q then (-1 : ℝ) else 0))
      (fun t : Fin 2 => if i = Fin.last nQ then (if t = 0 then (1 : ℝ) else -1) else 0) r

/-- Right-hand side of the uncertainty set of (EC.4): `1` for `ξ_q ≤ 1`, `0` for `−ξ_q ≤ 0`,
`1` for `ξ_{Q+1} ≤ 1`, `−1` for `−ξ_{Q+1} ≤ −1`. -/
def ec4b (nQ : ℕ) : Fin ((nQ + nQ) + 2) → ℝ :=
  fun r =>
    Fin.addCases (Fin.addCases (fun _ => (1 : ℝ)) (fun _ => 0))
      (fun t : Fin 2 => if t = 0 then (1 : ℝ) else -1) r

/-- Every point of `{0,1}^Q` is a 0/1 vector. -/
theorem binaryCube_binary (nQ : ℕ) : ∀ y ∈ binaryCube nQ, ∀ j, y j = 0 ∨ y j = 1 := by
  intro y hy j
  simp only [binaryCube, Finset.mem_image, Finset.mem_univ, true_and] at hy
  obtain ⟨β, rfl⟩ := hy
  unfold boolVec
  cases β j <;> simp

/-- `|{0,1}^Q| = 2^Q`. -/
theorem binaryCube_card (nQ : ℕ) : (binaryCube nQ).card = 2 ^ nQ := by
  unfold binaryCube
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  intro β β' h
  funext q
  have := congrFun h q
  unfold boolVec at this
  cases hb : β q <;> cases hb' : β' q <;> simp_all

/-- The augmented uncertainty set of (EC.4) consists of the vectors with `0 ≤ ξ_q ≤ 1` and
`ξ_{Q+1} = 1`. -/
theorem ec4_Xi_iff (nQ : ℕ) (ξ : Fin (nQ + 1) → ℝ) :
    ec4A nQ *ᵥ ξ ≤ ec4b nQ ↔
      (∀ q : Fin nQ, 0 ≤ ξ (Fin.castSucc q) ∧ ξ (Fin.castSucc q) ≤ 1) ∧ ξ (Fin.last nQ) = 1 := by
  have h1 : ∀ q : Fin nQ, (ec4A nQ *ᵥ ξ) (Fin.castAdd 2 (Fin.castAdd nQ q)) = ξ (Fin.castSucc q) := by
    intro q
    simp only [ec4A, mulVec, dotProduct, of_apply, Fin.addCases_left]
    simp
  have h2 : ∀ q : Fin nQ,
      (ec4A nQ *ᵥ ξ) (Fin.castAdd 2 (Fin.natAdd nQ q)) = -ξ (Fin.castSucc q) := by
    intro q
    simp only [ec4A, mulVec, dotProduct, of_apply, Fin.addCases_left, Fin.addCases_right]
    simp
  have h3 : (ec4A nQ *ᵥ ξ) (Fin.natAdd (nQ + nQ) 0) = ξ (Fin.last nQ) := by
    simp only [ec4A, mulVec, dotProduct, of_apply, Fin.addCases_right]
    simp
  have h4 : (ec4A nQ *ᵥ ξ) (Fin.natAdd (nQ + nQ) 1) = -ξ (Fin.last nQ) := by
    simp only [ec4A, mulVec, dotProduct, of_apply, Fin.addCases_right]
    simp
  rw [Pi.le_def]
  simp only [Fin.forall_fin_add, Fin.forall_fin_two]
  simp only [h1, h2, h3, h4, ec4b, Fin.addCases_left, Fin.addCases_right]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨fun q => ⟨by linarith [hb q], ha q⟩, ?_⟩
    simp at hc hd
    linarith
  · rintro ⟨ha, hc⟩
    refine ⟨⟨fun q => (ha q).2, fun q => by linarith [(ha q).1]⟩, ?_, ?_⟩ <;> simp [hc]

/-- The instance (EC.4) of 𝒫 from the proof of Theorem 4 (p. ec5), for `Q = nQ` uncertain
parameters: no first-stage decision (`N = 0`, `𝒳` the single point of `ℝ^0`), `𝒴 = {0,1}^Q`,
zero objective (`C = 0`, `Q = 0`), `T = 0`, second-stage constraints
`y_q − ξ_q ≤ 1/2`, `ξ_q − y_q ≤ 1/2` (`q = 1, …, Q`), and uncertainty set `[0,1]^Q`. The affine
right-hand side `ξ_q + 1/2` is written with the auxiliary parameter `ξ_{Q+1}` and the constraint
`ξ_{Q+1} = 1`, as p. 6 prescribes, so the parameter lives in `ℝ^{Q+1}`, `L = 2Q`, `R = 2Q + 2`. -/
noncomputable def inst (nQ : ℕ) : Problem 0 nQ (nQ + nQ) (nQ + 1) ((nQ + nQ) + 2) where
  C := 0
  Q := 0
  T := 0
  W := ec4W nQ
  H := ec4H nQ
  A := ec4A nQ
  b := ec4b nQ
  X := Set.univ
  Y := binaryCube nQ
  X_binary := fun _ _ i => i.elim0
  Y_binary := binaryCube_binary nQ
  Xi_nonempty := ⟨fun _ => 1, by
    show ec4A nQ *ᵥ _ ≤ ec4b nQ
    rw [ec4_Xi_iff]
    exact ⟨fun _ => ⟨zero_le_one, le_rfl⟩, rfl⟩⟩
  Xi_bounded := by
    refine (Metric.isBounded_Icc (0 : Fin (nQ + 1) → ℝ) 1).subset ?_
    intro ξ hξ
    have h := (ec4_Xi_iff nQ ξ).1 hξ
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> induction i using Fin.lastCases with
    | last => simp [h.2]
    | cast q => simp [(h.1 q).1, (h.1 q).2]

end KAdaptability.ConstrGap


