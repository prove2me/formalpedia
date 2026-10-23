-- Prove2me | Definitions.Def_LoockCVQEC_RepCode_Protocol
-- name    : LoockCVQEC_RepCode_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:32.15783+00:00
-- url     : https://prove2.me/theorems/26c8469f-2729-4d9e-afbb-ea516664c8ad
-- title:
--   Coherent and squeezed-vacuum Wigner functions, the tritter, the stochastic x-displacement channel, decoding, homodyne with feedforward, output and fidelity (Eqs. (1)–(5), pp. 1–2; Sec. IV, pp. 2–4)
-- statement:
--   This file fixes the model of Sections II–IV of van Loock's note: a Gaussian three-mode repetition code that protects one optical mode against a stochastic, fixed-size displacement error. Every state is described by its Wigner function, a real function on phase space; a single mode has coordinates $(x,p)\in\mathbb R^2$, three modes have $x=(x_1,x_2,x_3)$ and $p=(p_1,p_2,p_3)$. The vacuum has variance $1/4$ in each quadrature.
--
--   1. **Input** (Eq. (2), p. 2): the coherent state $|\bar x_1+i\bar p_1\rangle$,
--   $$W_{\mathrm{in}}(x_1,p_1)=\frac2\pi\exp\!\big[-2(x_1-\bar x_1)^2-2(p_1-\bar p_1)^2\big].$$
--   2. **Ancillas** (Eq. (4), p. 2): x-squeezed vacua with squeezing parameter $r$,
--   $$W_{\mathrm{anc}}(x_k,p_k)=\frac2\pi\exp\!\big[-2e^{2r}x_k^2-2e^{-2r}p_k^2\big],\qquad k=2,3,$$
--   and the product state (Eq. (5)) $W(x,p)=W_{\mathrm{in}}(x_1,p_1)W_{\mathrm{anc}}(x_2,p_2)W_{\mathrm{anc}}(x_3,p_3)$.
--   3. **Tritter** (p. 2): two beam splitters with transmittances $1:2$ and $1:1$, acting on $x$ and on $p$ by the orthogonal matrix
--   $$D=\begin{pmatrix}1/\sqrt3&1/\sqrt3&1/\sqrt3\\ \sqrt{2/3}&-1/\sqrt6&-1/\sqrt6\\ 0&1/\sqrt2&-1/\sqrt2\end{pmatrix}.$$
--   Encoding is $W_{\mathrm{enc}}(x,p)=W(Dx,Dp)$; decoding ("inverting the tritter") is $W_{\mathrm{dec}}(x,p)=W'(D^{\mathsf T}x,D^{\mathsf T}p)$.
--   4. **Channel** (Eqs. (1), (3), pp. 1–2): with probability $\gamma$ a mode is displaced by $\bar x_2$ in $x$, otherwise it is unchanged. On mode $k$ of a three-mode state this is
--   $$(N_kW)(x,p)=(1-\gamma)W(x,p)+\gamma W(x-\bar x_2e_k,p),$$
--   and the three channels act independently: $W'_{\mathrm{enc}}=N_1N_2N_3W_{\mathrm{enc}}$. The decoded state is $W_{\mathrm{dec}}=\mathrm{decode}(W'_{\mathrm{enc}})$.
--   5. **Syndrome measurement, recovery and averaging** (pp. 3–4): x-homodyne detection of modes 2 and 3 gives outcomes $x_2,x_3$; mode 1 is then displaced by a feedforward $\varphi(x_2,x_3)$, which depends on the outcomes only; the outcomes are averaged. The output of mode 1 is
--   $$W_r(x_1,p_1)=\int_{\mathbb R^4}W_{\mathrm{dec}}\big(x_1+\varphi(x_2,x_3),x_2,x_3;\,p_1,p_2,p_3\big)\,dx_2\,dx_3\,dp_2\,dp_3 .$$
--   6. **Direct transmission**: $(1-\gamma)W(x,p)+\gamma W(x-\bar x_2,p)$ for a single mode.
--   7. **Fidelity** with the pure coherent input: $F(W)=\pi\int_{\mathbb R^2}W_{\mathrm{in}}W\,dx\,dp$.
--   8. **Bookkeeping for the feedforward hypothesis.** For a set $S\subseteq\{1,2,3\}$ of erring channels, $\sigma(S)$ is the pair of the last two coordinates of $D(\bar x_2\mathbf 1_S)$, the ancilla displacement this error pattern causes after decoding. The paper's feedforward for pattern $S$, read off Eq. (9), is $x_2/\sqrt2$ for $\{1\}$, $\sqrt{2/3}\,x_3$ for $\{2\}$, $-\sqrt{2/3}\,x_3$ for $\{3\}$, $2\sqrt{2/3}\,x_3$ for $\{1,2\}$, $-2\sqrt{2/3}\,x_3$ for $\{1,3\}$, $-\sqrt2\,x_2$ for $\{2,3\}$, and $0$ otherwise.
--   9. The x-marginal of a squeezed ancilla, $\int W_{\mathrm{anc}}(y,p)\,dp=\sqrt{2/(\pi e^{-2r})}\,e^{-2e^{2r}y^2}$, as printed in Eq. (9).
--
--   These are the objects of Eq. (10) and of the displays (6)–(9) leading to it.
--
--   **Formalization Note** Mode $j$ of the paper is Lean index $j-1$ (`Fin 3`). A displacement by $+d$ is $W(x-d)$. The output integral is the Bochner integral over $(\mathbb R\times\mathbb R)\times(\mathbb R\times\mathbb R)$ with variables $((x_2,x_3),(p_2,p_3))$; for a non-integrable integrand it would return $0$, which is why the goal assumes a measurable feedforward. The fidelity formula $\pi\int W_{\mathrm{in}}W$ is the overlap $\langle\psi|\rho|\psi\rangle$ for the pure input in the units of Eq. (2).
-- source:
--   van Loock, A note on quantum error correction with continuous variables, arXiv:0811.3616v1, pp. 1–4, Eqs. (1)–(5), Sec. IV (pp. 2–4)

import Mathlib

namespace LoockCVQEC.RepCode

open Real MeasureTheory Matrix

/-- Eq. (2): Wigner function of the coherent state `|x̄₁ + i p̄₁⟩` (vacuum variance `1/4`). -/
noncomputable def inW (xb pb x p : ℝ) : ℝ :=
  2 / π * exp (-2 * (x - xb) ^ 2 - 2 * (p - pb) ^ 2)

/-- Eq. (4): Wigner function of the x-squeezed vacuum with squeezing parameter `r`. -/
noncomputable def ancW (r x p : ℝ) : ℝ :=
  2 / π * exp (-2 * exp (2 * r) * x ^ 2 - 2 * exp (-2 * r) * p ^ 2)

/-- Eq. (5): the product state of the signal mode (index 0) and the two ancillas (indices 1, 2). -/
noncomputable def prodW (xb pb r : ℝ) (x p : Fin 3 → ℝ) : ℝ :=
  inW xb pb (x 0) (p 0) * ancW r (x 1) (p 1) * ancW r (x 2) (p 2)

/-- The tritter (two beam splitters, transmittances 1 : 2 and 1 : 1) as an orthogonal matrix. -/
noncomputable def tritter : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / √3, 1 / √3, 1 / √3;
     √(2 / 3), -(1 / √6), -(1 / √6);
     0, 1 / √2, -(1 / √2)]

/-- Encoding: the tritter acts on a three-mode Wigner function, `W_enc(x, p) = W(D x, D p)`. -/
noncomputable def encode (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (x p : Fin 3 → ℝ) : ℝ :=
  W (tritter *ᵥ x) (tritter *ᵥ p)

/-- Decoding (inverse tritter): `W_dec(y, q) = W(Dᵀ y, Dᵀ q)`. -/
noncomputable def decode (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) (x p : Fin 3 → ℝ) : ℝ :=
  W (tritterᵀ *ᵥ x) (tritterᵀ *ᵥ p)

/-- Eqs. (1), (3) acting on mode `k`: with probability `γ` the mode is displaced by `d` in `x`. -/
def errMode (γ d : ℝ) (k : Fin 3) (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (x p : Fin 3 → ℝ) : ℝ :=
  (1 - γ) * W x p + γ * W (x - Pi.single k d) p

/-- The three independent channels, one on every mode. -/
def noisy (γ d : ℝ) (W : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ :=
  errMode γ d 0 (errMode γ d 1 (errMode γ d 2 W))

/-- The decoded three-mode state `W_dec` of Eq. (8), computed from the protocol. -/
noncomputable def decoded (xb pb r γ d : ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ :=
  decode (noisy γ d (encode (prodW xb pb r)))

/-- Output of mode 1: homodyne of modes 2, 3 (integrate `p₂, p₃`), feedforward displacement of
mode 1 by `φ(x₂, x₃)`, and averaging over the outcomes `x₂, x₃`.
The variable `z = ((x₂, x₃), (p₂, p₃))`. -/
noncomputable def output (xb pb r γ d : ℝ) (φ : ℝ → ℝ → ℝ) (x1 p1 : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × (ℝ × ℝ),
    decoded xb pb r γ d ![x1 + φ z.1.1 z.1.2, z.1.1, z.1.2] ![p1, z.2.1, z.2.2]

/-- Direct transmission of a single mode through the channel of Eqs. (1), (3). -/
def directOut (γ d : ℝ) (W : ℝ → ℝ → ℝ) (x p : ℝ) : ℝ :=
  (1 - γ) * W x p + γ * W (x - d) p

/-- Fidelity with the pure coherent input of Eq. (2): `F = π ∫ W_in W dx dp`. -/
noncomputable def fidelity (xb pb : ℝ) (W : ℝ → ℝ → ℝ) : ℝ :=
  π * ∫ v : ℝ × ℝ, inW xb pb v.1 v.2 * W v.1 v.2

/-- The x-displacement vector of the error pattern `S` (the set of erring channels). -/
def errVec (d : ℝ) (S : Finset (Fin 3)) : Fin 3 → ℝ :=
  fun i => if i ∈ S then d else 0

/-- The ancilla displacements `(x₂, x₃)` produced by error pattern `S` after decoding. -/
noncomputable def syndrome (d : ℝ) (S : Finset (Fin 3)) : ℝ × ℝ :=
  ((tritter *ᵥ errVec d S) 1, (tritter *ᵥ errVec d S) 2)

/-- The feedforward displacement the paper applies to mode 1 for error pattern `S` (Eq. (9)),
as a function of the homodyne results `x₂, x₃`; `0` for no error and for all three errors. -/
noncomputable def paperFeedforward (S : Finset (Fin 3)) (y2 y3 : ℝ) : ℝ :=
  if S = {0} then y2 / √2
  else if S = {1} then √(2 / 3) * y3
  else if S = {2} then -(√(2 / 3) * y3)
  else if S = {0, 1} then 2 * √(2 / 3) * y3
  else if S = {0, 2} then -(2 * √(2 / 3) * y3)
  else if S = {1, 2} then -(√2 * y2)
  else 0

/-- The x-marginal of the squeezed ancilla, `∫ W_anc(y, p) dp`, as it appears in Eq. (9). -/
noncomputable def sqzMarg (r y : ℝ) : ℝ :=
  √(2 / (π * exp (-2 * r))) * exp (-2 * exp (2 * r) * y ^ 2)

end LoockCVQEC.RepCode


