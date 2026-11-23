-- Prove2me | Definitions.Def_PlatonicJEPA_Basic
-- name    : PlatonicJEPA_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T12:14:34.422307+00:00
-- url     : https://prove2.me/theorems/8bd60d6a-f8c1-4302-a2c6-289763d43eeb
-- title:
--   Platonic JEPAs: finite world, positive-pair laws, JEPA objectives, spectral and alignment quantities
-- statement:
--   Objects of Section 2 and Appendix A.1 of Balestriero and LeCun (2026).
--
--   1. **World and positive pairs.** A world is a finite set $Z$ of states with probabilities $p(z)>0$, $\sum_z p(z)=1$. A positive-pair law is a symmetric law $\pi(z,z')\ge0$ on pairs of states whose marginals both equal $p$.
--   2. **Embeddings and rotations.** An embedding is $h:Z\to\mathbb{R}^k$, with $\|a\|^2=\sum_i a_i^2$. An orthogonal $Q\in O(k)$ acts by $a\mapsto Qa$. The law of the embeddings is $\sum_z p(z)\,\delta_{h(z)}$.
--   3. **JEPA objective (eq. 1).** For a prediction term $\ell$ and an anti-collapse term $\Omega$ that depends on $h$ only through the law of its embeddings and may equal $+\infty$, $L_\pi(h)=\sum_{z,z'}\pi(z,z')\,\ell(h(z),h(z'))+\Omega(h)$. A modality that renders $z$ as $g(z)$ trains an encoder $f$ on its observations with $L_m(f)=\sum_{z,z'}\pi(z,z')\,\ell(f(g(z)),f(g(z')))+\Omega(f\circ g)$.
--   4. **Spectral JEPA (Proposition 1).** $h$ is whitened if $\sum_z p(z)h(z)=0$ and $\sum_z p(z)h(z)h(z)^\top=I_k$. The prediction loss is $\sum_{z,z'}\pi(z,z')\|h(z)-h(z')\|^2$, and a spectral minimiser minimises it among whitened embeddings.
--   5. **Spectrum.** $K_\pi=D^{-1/2}\Pi D^{-1/2}$ with $D=\mathrm{diag}(p)$ and $\Pi_{zz'}=\pi(z,z')$. Its eigenvalues are $\mu_0\ge\mu_1\ge\cdots$ with multiplicity. The top space is the span of the eigenvectors of $K_\pi$ with eigenvalue at least $\mu_k$. $\|\cdot\|_2$ and $\|\cdot\|_F$ are the spectral and Frobenius norms.
--   6. **Nuisance (Section 2.3).** An observation of state $z$ carries a nuisance $\nu\sim q$, drawn independently of $z$. An encoder is written $e(z,\nu)$ and is centred and whitened under $p(z)q(\nu)$. $C_f$ is the covariance of $E[e\mid z]=\sum_\nu q(\nu)e(z,\nu)$, and the scene-explained fraction is $\rho(f)=\operatorname{tr}C_f^{1/2}/k$. A good-view JEPA's positive-pair law on observations is $\pi(z,z')q(\nu)q(\nu')$.
--   7. **Next-token prediction (eq. 6).** For a context embedding $h\in\mathbb{R}^k$ and token vectors $w_v$, $A(h)=\log\sum_v e^{\langle h,w_v\rangle}$ and the loss is $-\langle h,w_y\rangle+A(h)$.
--
--   **Formalization Note** The eigenvalues $\mu_i$ are the roots of the characteristic polynomial of $K_\pi$, sorted in decreasing order. The paper's convention $\mu_{|Z|}=-\infty$ is written in each statement as a hypothesis that applies only when $k+1<|Z|$. $\operatorname{tr}C_f^{1/2}$ is the sum of the square roots of the eigenvalues of $C_f$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2 (eq. 1, eq. 6) and Appendix A.1

import Mathlib

/-!
Balestriero and LeCun, *Proving and Improving the Platonic Representation Hypothesis with JEPAs*,
arXiv:2610.39302v1 (2026): the finite world, positive-pair laws, JEPA objectives, spectral
quantities and alignment quantities of Section 2 and Appendix A.1.
-/

open MeasureTheory

noncomputable section

namespace PlatonicJEPA

variable {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}

/-- Squared Euclidean norm of an embedding `v ∈ ℝ^k`. -/
def sqNorm (v : Fin k → ℝ) : ℝ := ∑ i, v i ^ 2

/-- Section 2.1: `p` is a probability on the finite world with `p(z) > 0`, and `π` is a symmetric
law on pairs of world states, both of whose marginals equal `p`. -/
def IsPairLaw (p : Z → ℝ) (π : Z → Z → ℝ) : Prop :=
  (∀ z, 0 < p z) ∧ (∑ z, p z = 1) ∧ (∀ z z', 0 ≤ π z z') ∧ (∀ z z', π z z' = π z' z) ∧
    (∀ z, ∑ z', π z z' = p z)

/-- The law of the embeddings `h(z)`, `z ∼ p`. -/
def embLaw (p : Z → ℝ) (h : Z → Fin k → ℝ) : Measure (Fin k → ℝ) :=
  ∑ z, ENNReal.ofReal (p z) • Measure.dirac (h z)

/-- Eq. (1) written on world states: `L_π(h) = E_{(z,z')∼π} ℓ(h z, h z') + Ω(h)`, where the
anti-collapse term `Ω` depends on `h` only through the law of its embeddings and may be `+∞`. -/
def worldLoss (p : Z → ℝ) (π : Z → Z → ℝ) (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (Ω : Measure (Fin k → ℝ) → EReal) (h : Z → Fin k → ℝ) : EReal :=
  ((∑ z, ∑ z', π z z' * ℓ (h z) (h z') : ℝ) : EReal) + Ω (embLaw p h)

/-- Eq. (1): the objective of a JEPA of a modality that renders state `z` as `g z`, for an
encoder `f` on that modality's observations. -/
def modalityLoss {X : Type*} (p : Z → ℝ) (π : Z → Z → ℝ) (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (Ω : Measure (Fin k → ℝ) → EReal) (g : Z → X) (f : X → Fin k → ℝ) : EReal :=
  ((∑ z, ∑ z', π z z' * ℓ (f (g z)) (f (g z')) : ℝ) : EReal) + Ω (embLaw p (f ∘ g))

/-- Rotation of an embedding by an orthogonal matrix. -/
def rot (Q : Matrix.orthogonalGroup (Fin k) ℝ) (v : Fin k → ℝ) : Fin k → ℝ :=
  (Q : Matrix (Fin k) (Fin k) ℝ).mulVec v

/-- `h` is centred and whitened under `p`: `E_p h = 0`, `E_p h hᵀ = I_k`. -/
def IsWhitened (p : Z → ℝ) (h : Z → Fin k → ℝ) : Prop :=
  (∀ i, ∑ z, p z * h z i = 0) ∧ (∀ i j, ∑ z, p z * h z i * h z j = if i = j then 1 else 0)

/-- The prediction term with `ℓ(a,b) = ‖a - b‖²`: `E_{(z,z')∼π} ‖h z - h z'‖²`. -/
def predLoss (π : Z → Z → ℝ) (h : Z → Fin k → ℝ) : ℝ :=
  ∑ z, ∑ z', π z z' * sqNorm (h z - h z')

/-- Proposition 1: `h` minimises `L_π` for `ℓ(a,b) = ‖a-b‖²` and `Ω` the whitening constraint. -/
def IsSpectralMin (p : Z → ℝ) (π : Z → Z → ℝ) (h : Z → Fin k → ℝ) : Prop :=
  IsWhitened p h ∧ ∀ h' : Z → Fin k → ℝ, IsWhitened p h' → predLoss π h ≤ predLoss π h'

/-- The normalised adjacency `K_π = D^{-1/2} Π D^{-1/2}`. -/
def kerMat (p : Z → ℝ) (π : Z → Z → ℝ) : Matrix Z Z ℝ :=
  fun z z' => π z z' / Real.sqrt (p z * p z')

/-- The eigenvalues `μ₀ ≥ μ₁ ≥ …` of `K_π`, with multiplicity, as the roots of its characteristic
polynomial sorted in decreasing order (`μ_i := 0` for `i ≥ |Z|`; statements never use those). -/
def eigs (p : Z → ℝ) (π : Z → Z → ℝ) (i : ℕ) : ℝ :=
  ((kerMat p π).charpoly.roots.sort (· ≥ ·)).getD i 0

/-- The span of the eigenvectors of `K_π` whose eigenvalue is at least `μ_k`. -/
def topSpace (p : Z → ℝ) (π : Z → Z → ℝ) (k : ℕ) : Submodule ℝ (Z → ℝ) :=
  ⨆ (μ : ℝ) (_ : eigs p π k ≤ μ), Module.End.eigenspace (Matrix.toLin' (kerMat p π)) μ

/-- Spectral (operator) norm of a real matrix. -/
def specNorm (A : Matrix Z Z ℝ) : ℝ :=
  sSup ((fun v : Z → ℝ => Real.sqrt (∑ z, (A.mulVec v z) ^ 2)) '' {v | ∑ z, v z ^ 2 ≤ 1})

/-- Frobenius norm of a real matrix. -/
def frobNorm (A : Matrix Z Z ℝ) : ℝ := Real.sqrt (∑ z, ∑ z', A z z' ^ 2)

section Nuisance

variable {N : Type*} [Fintype N]

/-- Section 2.3: an encoder of observations `g(z, ν)`, written as `e z ν = f(g(z, ν))`, is centred and
whitened on its observations, whose law is `p(z) q(ν)`. -/
def IsWhitenedObs (p : Z → ℝ) (q : N → ℝ) (e : Z → N → Fin k → ℝ) : Prop :=
  IsWhitened (fun x : Z × N => p x.1 * q x.2) (fun x => e x.1 x.2)

/-- `E[f(x) | z]` for an observation `x = g(z, ν)`, `ν ∼ q`. -/
def condMean (q : N → ℝ) (e : Z → N → Fin k → ℝ) (z : Z) : Fin k → ℝ :=
  fun i => ∑ ν, q ν * e z ν i

/-- `C_f = Cov E[f(x) | z]` (the encoder is centred, so this is the second-moment matrix). -/
def stateCov (p : Z → ℝ) (q : N → ℝ) (e : Z → N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∑ z, p z * condMean q e z i * condMean q e z j

/-- The scene-explained fraction `ρ(f) = tr C_f^{1/2} / k`, computed from the eigenvalues of
`C_f` (the roots of its characteristic polynomial, with multiplicity). -/
def rho (p : Z → ℝ) (q : N → ℝ) (e : Z → N → Fin k → ℝ) : ℝ :=
  (((stateCov p q e).charpoly.roots.map Real.sqrt).sum) / k

end Nuisance

/-- Proposition 3 (i): the positive-pair law of a good-view JEPA on observations `(z, ν)`:
`π(z, z') q(ν) q(ν')`. -/
def goodViewLaw {N : Type*} (π : Z → Z → ℝ) (q : N → ℝ) (x y : Z × N) : ℝ :=
  π x.1 y.1 * q x.2 * q y.2

/-- Eq. (6): the anti-collapse term of next-token prediction, `A(h) = log ∑_v exp ⟨h, w_v⟩`. -/
def ntpAntiCollapse {V : Type*} [Fintype V] (w : V → Fin k → ℝ) (h : Fin k → ℝ) : ℝ :=
  Real.log (∑ v, Real.exp (∑ i, h i * w v i))

/-- Eq. (6): the next-token loss `-⟨h, w_y⟩ + A(h)`. -/
def ntpLoss {V : Type*} [Fintype V] (w : V → Fin k → ℝ) (h : Fin k → ℝ) (y : V) : ℝ :=
  -(∑ i, h i * w y i) + ntpAntiCollapse w h

end PlatonicJEPA


