-- Prove2me | Definitions.Def_PrivGaussMS_Correction
-- name    : PrivGaussMS_Correction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:12:10.300067+00:00
-- url     : https://prove2.me/theorems/4a70da2a-b886-46aa-aeda-0c4866d243b7
-- title:
--   The auxiliary sampler: $D_A$, $\pi$, $w$, $q$, $Z_a$, $r_A$, the recipe (27), $h_{U,V}$ (24), $A_*(U,V)$, the decision probability (28) and Procedure 5
-- statement:
--   Write $T_0=\mathrm{diag}(I_d,n)$. For a simulated dataset $U$ (rows of a frame) and $A\subseteq[n]$, $D_A=\det T/\det T_{A^c}$ with $D_\emptyset=1$. Set $p=e^{-\lambda/8}/n$, $\pi(A)=p^{|A|}(1-p)^{n-|A|}$, $w=(1-p)^n$, $q=\lfloor n/3\rfloor$, $Z_a=\mathbb E_{\mathrm{uniform}}D_A^q$ ($Z_0=1$) and $r_A=D_A^q/Z_a$. For $a=|A|>0$, the recipe (27) draws $F_A$ as the first $a$ rows of a uniform $(n-1-2q)\times d$ frame and an independent uniform $d$-frame $H_A$ in $\mathcal H_A=\{u:1_n^Tu=0,\ u_i=0\ (i\in A)\}$, and sets
--   $$U=H_A(I_d-F_A^TF_A)^{1/2}+E_AF_A,$$
--   $E_A$ an orthonormal basis of the complement of $\mathcal H_A$ in $1_n^\perp$. The density ratio is $h_{U,V}(J,z)=f^{(|J|)}_{B(U)}(z)/f^{(|J|)}_{T_0}(z)$ on acceptance of the simulated test and $\eta^{-m}\mathbf 1\{J=\emptyset\}$ on rejection. The recorded set $A_*(U,V)$ is $[n]\setminus I_k$ on acceptance and the first $a_0$ rows deleted at threshold $\lambda$ on rejection.
--
--   **Procedure 5** draws a proposal $\zeta=(J,z)$ and independently $A\sim\pi$; if $|A|\ge k$ it returns $\mathrm{Priv}=0$. Otherwise it draws $U$ (uniform centered for $a=0$, by (27) for $a>0$) and $V\sim\mathrm{Lap}(2/\varepsilon)$, and if $A=A_*(U,V)$ sets $\mathrm{Priv}=1$ with probability
--   $$h_{U,V}(J,z)\,Z_a\Bigl(\frac{1-p}{p}\Bigr)^aD_A(U)^{-q},\tag{28}$$
--   and $\mathrm{Priv}=0$ otherwise. It returns the original proposal and the decision.
--
--   **Formalization Note** The Bernoulli choice uses a uniform $\tau\in[0,1]$ ($\mathrm{Priv}=1$ iff $\tau<(28)$), so its probability is (28) clamped to $[0,1]$; the clamp is shown inactive in the item for eq. (31). $E_A$ is Gram–Schmidt of $e_i-n^{-1}1_n$ ($i\in A$), and $H_A$ is realized through a Helmert basis of $\mathcal H_A$. The density ratio is $0$ where the denominator vanishes (p.51).
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), §B.4.3, pp.45–49, eqs. (24)–(28), Algorithm 5 (Procedure 5), p.49

import Mathlib
import Definitions.Def_PrivGaussMS_Sampler
import Definitions.Def_PrivGaussMS_CandidateDensity

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-!
# The auxiliary sampler: `D_A`, `π`, `w`, `q`, `Z_a`, `r_A`, the recipe (27), `h_{U,V}` (24),
# `A_*(U, V)`, the decision probability (28) and Procedure 5

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), §B.4.3, pp.45–49 (eqs. (24)–(28), Algorithm 5 "Proposal and branch
decision", p.49).

**Formalization Note.**
* `T0 d n = diag(I_d, n)` (p.44). The simulated dataset is the rows of a frame `U`.
* `DA x A = det T / det T_{Aᶜ}` with `D_∅ = 1` (pp.47–48); `pSel n λ = e^{−λ/8}/n`,
  `piSet n p A = p^{|A|}(1 − p)^{n−|A|}`, `wConst n λ = (1 − p)^n`, `qExp n = ⌊n/3⌋` (natural
  division); `Zconst n d A = E_uniform D_A^q` (Bochner integral) with `Z_∅ = 1`; `rA = D_A^q/Z_a`
  (p.48).
* (27): `F_A` is the first `a` rows of a uniform `(n − 1 − 2q) × d` frame and `H_A` a uniform
  `d`-frame in `H_A = {u : 1ᵀu = 0, u_i = 0 (i ∈ A)}`, realized as `K_A Q` with `Q` a uniform
  `(|Aᶜ| − 1) × d` frame and `K_A` the Helmert basis of the centered vectors on the coordinates `Aᶜ`;
  `E_A` is the Gram–Schmidt orthonormalization of `e_i − n⁻¹1_n` (`i ∈ A`, increasing), an
  orthonormal basis of the orthogonal complement of `H_A` in `1_n^⊥`. The paper fixes no basis.
  For `a = 0` the frame is uniform centered (p.49).
* `hUV`: on acceptance of the simulated test, `f^{(|J|)}_{B(U)}(z)/f^{(|J|)}_{T0}(z)` with ratio `0`
  where the denominator vanishes (p.51) — at `J = ∅` both densities are `1`, so `h = 1`; on
  rejection `η^{−m} 1{J = ∅}` (24). `z` lists the retained vectors in increasing position order.
* `Astar`: on acceptance `[n] \ I_k`; on rejection the first `a0` rows deleted by pruning at
  threshold `λ = u_0` (p.46). On the null event of fewer than `a0` deletions the list is shorter.
* Procedure 5 draws the proposal `ζ`, the set `A ∼ π` (`p` independently per index), the frame `U`
  (uniform centered for `A = ∅`, (27) for `0 < |A| < k`, not used for `|A| ≥ k`), `V ∼ Lap(2/ε)`
  and a uniform `τ ∈ [0, 1]`, and sets `Priv = 1` iff `|A| < k`, `A = A_*(U, V)` and `τ < (28)`.
  Thus `P{Priv = 1 | …} = min{1, max{0, (28)}}`; Lemma "eq. (31)" proves `(28) ∈ [0, 1]` there. The
  paper's "on probability-zero events where the simulated frame is exceptional, set `Priv = 0`"
  (p.51) changes no law and is not encoded.
-/

variable {n m d : ℕ}

/-- `T0 = diag(I_d, n)` (p.44). -/
def T0 (d n : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ := diagIb d n

open Classical in
/-- `D_A = det T / det T_{Aᶜ}`, with `D_∅ = 1` (pp.47–48). -/
noncomputable def DA (x : Fin n → Vec d) (A : Finset (Fin n)) : ℝ :=
  if A = ∅ then 1 else (Tstat x).det / (statI x Aᶜ).det

/-- `p = e^{−λ/8}/n` (p.47). -/
noncomputable def pSel (n lam : ℕ) : ℝ := Real.exp (-(lam : ℝ) / 8) / n

/-- `π(A) = p^{|A|}(1 − p)^{n−|A|}` (p.47). -/
noncomputable def piSet (n : ℕ) (p : ℝ) (A : Finset (Fin n)) : ℝ :=
  p ^ A.card * (1 - p) ^ (n - A.card)

/-- `w = π(∅) = (1 − p)^n` (p.47). -/
noncomputable def wConst (n lam : ℕ) : ℝ := (1 - pSel n lam) ^ n

/-- `q = ⌊n/3⌋` (p.48). -/
def qExp (n : ℕ) : ℕ := n / 3

open Classical in
/-- `Z_a = E_uniform D_A^q` over a uniform centered frame with `A` fixed; `Z_∅ = 1` (p.48). -/
noncomputable def Zconst (n d : ℕ) (A : Finset (Fin n)) : ℝ :=
  if A = ∅ then 1 else ∫ U, DA (rowsOf U) A ^ qExp n ∂(uniformCenteredFrame n d)

/-- `r_A(U) = D_A(U)^q/Z_a` (p.48). -/
noncomputable def rA (n d : ℕ) (A : Finset (Fin n)) (U : Matrix (Fin n) (Fin d) ℝ) : ℝ :=
  DA (rowsOf U) A ^ qExp n / Zconst n d A

/-- `E_A`: Gram–Schmidt of `e_i − n⁻¹ 1_n` (`i ∈ A`, increasing), as `n × |A|` columns. -/
noncomputable def EA (n : ℕ) (A : Finset (Fin n)) : Matrix (Fin n) (Fin A.card) ℝ :=
  fun i j => (InnerProductSpace.gramSchmidtNormed ℝ (fun l : Fin A.card =>
      EuclideanSpace.single (A.orderEmbOfFin rfl l) (1 : ℝ) -
        ((n : ℝ)⁻¹) • (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ)) : EuclideanSpace ℝ (Fin n))) j) i

/-- `K_A`: the Helmert basis of the centered vectors supported on `Aᶜ`, as `n × (|Aᶜ| − 1)`
columns; its column space is `H_A` (p.48). -/
noncomputable def KA (n : ℕ) (A : Finset (Fin n)) : Matrix (Fin n) (Fin (Aᶜ.card - 1)) ℝ :=
  fun i j => if h : i ∈ Aᶜ then helmert Aᶜ.card ((Aᶜ.orderIsoOfFin rfl).symm ⟨i, h⟩) j else 0

open Classical in
/-- The law of `U = H_A (I_d − F_AᵀF_A)^{1/2} + E_A F_A` (27); uniform centered for `A = ∅`. -/
noncomputable def law27 (n d : ℕ) (A : Finset (Fin n)) : Measure (Matrix (Fin n) (Fin d) ℝ) :=
  if A = ∅ then uniformCenteredFrame n d
  else ((uniformFrame (n - 1 - 2 * qExp n) d).prod (uniformFrame (Aᶜ.card - 1) d)).map fun p =>
    KA n A * p.2 * CFC.sqrt (1 - (firstRows A.card p.1)ᵀ * firstRows A.card p.1) +
      EA n A * firstRows A.card p.1

open Classical in
/-- The retained position set `J` of a partial batch. -/
noncomputable def retained (ζ : PartialBatch m d) : Finset (Fin m) :=
  Finset.univ.filter fun j => (ζ j).isSome

/-- The retained vectors `z ∈ ℝ^{|J|×d}` of a partial batch, in increasing position order. -/
noncomputable def retainedMat (ζ : PartialBatch m d) :
    Matrix (Fin (retained ζ).card) (Fin d) ℝ :=
  fun i l => WithLp.ofLp ((ζ ((retained ζ).orderEmbOfFin rfl i)).getD 0) l

/-- Acceptance of the stability test of Algorithm 4 on the simulated dataset `U` with draw `V`. -/
def simAccept (n : ℕ) (lam k a0 : ℕ) (ℓ : ℝ) (U : Matrix (Fin n) (Fin d) ℝ) (V : ℝ) : Prop :=
  (score (rowsOf U) k lam : ℝ) + clip ℓ V < a0 + ℓ

open Classical in
/-- The density ratio `h_{U,V}(J, z)` of (24). -/
noncomputable def hUV (n m : ℕ) (lam k a0 : ℕ) (ℓ η : ℝ) (U : Matrix (Fin n) (Fin d) ℝ)
    (V : ℝ) (ζ : PartialBatch m d) : ℝ :=
  if simAccept n lam k a0 ℓ U V then
    (if candDensity n (retained ζ).card (T0 d n) (retainedMat ζ) = 0 then 0
     else candDensity n (retained ζ).card (Bstat (rowsOf U) k lam) (retainedMat ζ) /
       candDensity n (retained ζ).card (T0 d n) (retainedMat ζ))
  else if retained ζ = ∅ then η⁻¹ ^ m else 0

open Classical in
/-- The recorded set `A_*(U, V)` (p.46). -/
noncomputable def Astar (n : ℕ) (lam k a0 : ℕ) (ℓ : ℝ) (U : Matrix (Fin n) (Fin d) ℝ)
    (V : ℝ) : Finset (Fin n) :=
  if simAccept n lam k a0 ℓ U V then recordedSet (rowsOf U) k lam
  else ((prune (rowsOf U) (lam : ℝ)).deleted.take a0).toFinset

/-- The decision probability `h_{U,V}(J, z) Z_a ((1 − p)/p)^a D_A(U)^{−q}` of (28). -/
noncomputable def decisionProb (n m : ℕ) (lam k a0 : ℕ) (ℓ η : ℝ) (ζ : PartialBatch m d)
    (A : Finset (Fin n)) (U : Matrix (Fin n) (Fin d) ℝ) (V : ℝ) : ℝ :=
  hUV n m lam k a0 ℓ η U V ζ * Zconst n d A *
    ((1 - pSel n lam) / pSel n lam) ^ A.card * (DA (rowsOf U) A)⁻¹ ^ qExp n

open Classical in
/-- The joint law of the guessed set `A ∼ π` and the simulated frame `U` given `A`. -/
noncomputable def setFrameLaw (n d k lam : ℕ) :
    Measure (Finset (Fin n) × Matrix (Fin n) (Fin d) ℝ) :=
  ∑ A : Finset (Fin n), ENNReal.ofReal (piSet n (pSel n lam) A) •
    (Measure.dirac A).prod (if A.card < k then law27 n d A else uniformCenteredFrame n d)

open Classical in
/-- Procedure 5 (Algorithm 5, p.49): the joint law of the proposal `ζ` and the decision `Priv`. -/
noncomputable def procedure5 (n m d : ℕ) (lam k a0 : ℕ) (ℓ ε η : ℝ) :
    Measure (PartialBatch m d × Bool) :=
  ((proposalLaw n m d η).prod
      ((setFrameLaw n d k lam).prod ((laplace (2 / ε)).prod unif01))).map fun p =>
    (p.1, decide (p.2.1.1.card < k ∧ p.2.1.1 = Astar n lam k a0 ℓ p.2.1.2 p.2.2.1 ∧
      p.2.2.2 < decisionProb n m lam k a0 ℓ η p.1 p.2.1.1 p.2.1.2 p.2.2.1))

end PrivGaussMS


