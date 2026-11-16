-- Prove2me | Definitions.Def_GL2QFT_Supplement_AGammaGates
-- name    : GL2QFT_Supplement_AGammaGates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:39:24.964256+00:00
-- url     : https://prove2.me/theorems/426f8c31-56cd-4294-83a5-cb1f458a1435
-- title:
--   The gates $D_\gamma$, $\mathfrak F_\times^\dagger$, $B_\gamma$, $\mathfrak F_\times\oplus\mathfrak F_{\ker N}$, $R_{{\rm fix},\gamma}$, $R_{{\rm exc},\gamma}$ of §6.5.1
-- statement:
--   The gates of the $A_\gamma$-circuit (Figure 14, Definitions 6.16–6.21), on the source register $|c_\infty\rangle\leftrightarrow|0\rangle$, $|c_\alpha\rangle\leftrightarrow|\alpha\rangle$ (143).
--
--   1. $D_\gamma|c_\infty\rangle=|c_\infty\rangle$, $D_\gamma|c_\alpha\rangle=\zeta_{\alpha,b}|c_\alpha\rangle$ if $\alpha\neq b=\alpha^{-1}\gamma$ and $|c_\alpha\rangle$ otherwise, $\zeta_{\alpha,\beta}=\chi_\beta(-1)g_q(\alpha^{-1}\beta)/\sqrt q$ (127), (148)–(149).
--   2. $\mathfrak F_\times^\dagger$, the adjoint of $\mathfrak F_\times|a\rangle=(q-1)^{-1/2}\sum_\alpha\chi_\alpha(a)|\alpha\rangle$, fixing $|c_\infty\rangle=|0\rangle$.
--   3. The branching map $B_\gamma:\mathbb C[\mathbb F_q]\to\mathbb C^2\otimes\mathbb C[\mathbb F^*_{q^2}]$ (151)–(152), with $\theta_0(h)=e^{2\pi ik/(q^2-1)}$ for $\chi_\gamma(g)=e^{2\pi ik/(q-1)}$.
--   4. Admissible branch transforms: $\mathfrak F_\times|{\rm sp},r\rangle=(q-1)^{-1/2}\sum_\delta\chi_\delta(r)|{\rm sp},\delta\rangle$ for $r\in\mathbb F^*_q$ and $\mathfrak F_{\ker N}|{\rm ns},r\rangle=(q+1)^{-1/2}\sum_\nu\nu(r)|{\rm ns},\theta_0\nu\rangle$ for $r\in\ker N$ (153), any extension elsewhere.
--   5. Admissible label-fixing gates $R_{{\rm fix},\gamma}$ (154)–(155): symmetric combinations of non-fixed split pairs to $|I_{\delta,\gamma\delta^{-1}}\rangle$, of non-fixed Frobenius pairs to $|\pi_\theta\rangle$, antisymmetric combinations to unused labels, and for $\delta^2=\gamma$
--   $$R_{\rm fix}|{\rm sp},\delta\rangle=\sqrt{\tfrac{q+1}{2q}}|{\rm St}_\delta\rangle+\sqrt{\tfrac{q-1}{2q}}|{\det}_\delta\rangle,\quad R_{\rm fix}|{\rm ns},\chi_\delta\circ N\rangle=\sqrt{\tfrac{q-1}{2q}}|{\rm St}_\delta\rangle-\sqrt{\tfrac{q+1}{2q}}|{\det}_\delta\rangle.$$
--   6. $R_{{\rm exc},\gamma}$ (156)–(157): for every $\alpha^2=\gamma$ it acts on the pair $(A_\gamma|c_\alpha\rangle,|{\det}_\alpha\rangle)$ by $\begin{pmatrix}-\chi_\alpha(-1)/\sqrt q&\sqrt{(q-1)/q}\\\sqrt{(q-1)/q}&\chi_\alpha(-1)/\sqrt q\end{pmatrix}$, and as the identity on the orthogonal complement.
--
--   **Formalization Note** All maps act on clean-work inputs; the work registers are suppressed. Labels are exponents: $\theta^q$ has label $qk$ and $\chi_\delta\circ N$ has label $(q+1)\delta$. A character $\nu$ of $\ker N$ is labelled by $\theta_0\nu$; $\nu(r)=\theta_{\theta-k}(w)$ for any $w$ with $w/w^q=r$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), eq. (127) p.45, eq. (143) p.46, Definitions 6.16–6.21 eqs. (148)–(157), pp.49–50 (PDF pp.46–47, 50–51)

import Definitions.Def_GL2QFT_AGamma

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace AGammaGates

open FieldData
open scoped Matrix ComplexConjugate

variable (D : FieldData)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), eq. (127), p.45 (PDF p.46): the Gauss sum
phase `ζ_{α,β} = χ_β(−1) g_q(α⁻¹β) / √q` (labels: `α⁻¹β` is `β − α`). -/
def zeta (α β : D.Lab) : ℂ := D.chi β (-1) * D.gauss (β - α) / (Real.sqrt D.q : ℂ)

/-- arXiv:2608.28573, Definition 6.16, eqs. (148)–(149), p.49 (PDF p.50): the phase gate
`D_γ|c_∞⟩ = |c_∞⟩`, `D_γ|c_α⟩ = ζ_{α,b}|c_α⟩` if `α ≠ b` and `|c_α⟩` if `α = b`, `b = α⁻¹γ`.
The input register is `Option Lab`: `none` is `|c_∞⟩`, `some α` is `|c_α⟩` (143). -/
def Dgate (γ : D.Lab) : Matrix (Option D.Lab) (Option D.Lab) ℂ :=
  Matrix.diagonal fun c =>
    match c with
    | none => 1
    | some α => if α ≠ γ - α then zeta D α (γ - α) else 1

/-- arXiv:2608.28573, Definition 6.17, p.49, with eq. (120), p.41: `F†_×`, the adjoint of
`F_×|a⟩ = (q−1)^{−1/2} Σ_{α ∈ X_q} χ_α(a)|α⟩` (`a ∈ F*_q`), fixing `|c_∞⟩ = |0⟩`: from the source
register (`|c_∞⟩ ↔ |0⟩`, `|c_α⟩ ↔` the character label `α`) to `ℂ[F_q]`,
`F†_×|c_α⟩ = (q−1)^{−1/2} Σ_{t ∈ F*_q} conj(χ_α(t)) |t⟩`. -/
def FxDag : Matrix D.Fq (Option D.Lab) ℂ :=
  Matrix.of fun t c =>
    match c with
    | none => if t = 0 then 1 else 0
    | some α => if t = 0 then 0 else isqrt (D.q - 1) * conj (D.chi α t)

/-- arXiv:2608.28573, Definition 6.18, p.49: `θ₀`, the character of `F*_{q²}` with
`θ₀(h) = e^{2πik/(q²−1)}` where `χ_γ(g) = e^{2πik/(q−1)}`, `0 ≤ k ≤ q − 2`: the exponent label
`k = γ.val` read in `ZMod (q² − 1)`. -/
def theta0Lab (γ : D.Lab) : D.Lab2 := (γ.val : D.Lab2)

/-- arXiv:2608.28573, Definition 6.18, eqs. (151)–(152), p.49 (PDF p.50): the quadratic branching
map `B_γ : ℂ[F_q] → ℂ² ⊗ ℂ[F*_{q²}]` (row `(false, r)` is `|sp, r⟩`, `(true, r)` is `|ns, r⟩`):
* `t = 0`: `(|sp, 1⟩ + |ns, 1⟩)/√2`;
* `t = 1/4`, `char F_q` odd: `χ_γ(1/2)(|sp, 1⟩ − |ns, 1⟩)/√2`;
* otherwise, if `X² − X + t` has roots `x, y ∈ F_q`: `(χ_γ(y)|sp, x/y⟩ + χ_γ(x)|sp, y/x⟩)/√2`;
* otherwise (roots `z, z^q ∈ F_{q²}`): `(−θ₀(z)|ns, z/z^q⟩ − θ₀(z^q)|ns, z^q/z⟩)/√2`.

**Formalization Note** The two terms of the generic cases are the sum over the two roots `x` of
`X² − X + t` (then `y = 1 − x`), resp. over the two roots `z ∈ F_{q²}`. The unitary extension of
`B_γ` to a larger register (p.49) acts on clean-work inputs as this isometry; the theorem is
stated on clean-work inputs, where every extension agrees with it. -/
def Bgate (γ : D.Lab) : Matrix (Bool × D.Fq2) D.Fq ℂ :=
  Matrix.of fun br t =>
    if t = 0 then
      (if br.2 = 1 then isqrt 2 else 0)
    else if ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹ then
      (if br.2 = 1 then isqrt 2 * D.chi γ (2 : D.Fq)⁻¹ * (if br.1 then -1 else 1) else 0)
    else if ∃ x : D.Fq, x ^ 2 - x + t = 0 then
      (if br.1 then 0 else
        isqrt 2 * ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0),
          if br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) then D.chi γ (1 - x) else 0)
    else
      (if br.1 then
        -(isqrt 2 * ∑ z ∈ Finset.univ.filter
            (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0),
          if br.2 = z / z ^ D.q then D.theta (theta0Lab D γ) z else 0)
      else 0)

/-- The output labels of the two branch transforms: `|sp, δ⟩`, `δ ∈ X_q` (`inl δ`), and `|ns, θ⟩`
with `θ = θ₀ν` a character of `F*_{q²}` restricting to `χ_γ` (`inr θ`, `θ|_{F*_q} = χ_γ`). -/
abbrev BranchOut (γ : D.Lab) : Type := D.Lab ⊕ {θ : D.Lab2 // D.restrLab θ = γ}

/-- A character `ν` of `ker N` pulled back along `z ↦ z/z^q` is a character `θ_m` of `F*_{q²}`
trivial on `F*_q`; its value at `r ∈ ker N` is `ν(r) = θ_m(w)` for any `w` with `w/w^q = r`
(`ker N = {w/w^q}`, p.49). -/
def kerChar (m : D.Lab2) (r : D.Fq2) : ℂ :=
  if h : ∃ w : D.Fq2, w ≠ 0 ∧ w / w ^ D.q = r then D.theta m (Classical.choose h) else 0

/-- arXiv:2608.28573, Definition 6.19, eq. (153), p.50 (PDF p.51): an admissible branch transform
`F_× ⊕ F_{ker N}`: on `|sp, r⟩`, `r ∈ F*_q`, it acts as `F_×|sp, r⟩ = (q−1)^{−1/2} Σ_δ χ_δ(r)|sp, δ⟩`;
on `|ns, r⟩`, `r ∈ ker N`, as `F_{ker N}|ns, r⟩ = (q+1)^{−1/2} Σ_{ν ∈ (ker N)^} ν(r)|ns, θ₀ν⟩`. Its
action on the other basis states of `ℂ² ⊗ ℂ[F*_{q²}]` (the unitary extension) is left free. -/
def IsBranchTransform (γ : D.Lab) (M : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) : Prop :=
  (∀ r : D.Fq, r ≠ 0 → ∀ o : BranchOut D γ,
    M o (false, algebraMap D.Fq D.Fq2 r) =
      match o with
      | .inl δ => isqrt (D.q - 1) * D.chi δ r
      | .inr _ => 0) ∧
  (∀ r : D.Fq2, r ≠ 0 → r ^ (D.q + 1) = 1 → ∀ o : BranchOut D γ,
    M o (true, r) =
      match o with
      | .inl _ => 0
      | .inr θ => isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) r)

/-- The standard basis vector of `BranchOut`. -/
def eB (γ : D.Lab) (o : BranchOut D γ) : BranchOut D γ → ℂ := fun o' => if o' = o then 1 else 0

/-- The standard basis vector of the output label space `Irr ⊕ Unused`. -/
def eO {U : Type} (o : D.Irr ⊕ U) : D.Irr ⊕ U → ℂ := fun o' => if o' = o then 1 else 0

/-- arXiv:2608.28573, Definition 6.20, eqs. (154)–(155), p.50 (PDF p.51): an admissible label-fixing
gate `R_fix,γ` from the branch labels into `Irr ⊕ Unused` (irrep labels of `GL₂(F_q)` and unused
labels):
1. for a non-fixed split pair `(δ, δ⁻¹γ)`, i.e. a principal-series label `I_{α,β}`, `α ≺ β`,
   `αβ = γ`: `R_fix((|sp,α⟩ + |sp,β⟩)/√2) = |I_{α,β}⟩`;
2. for a non-fixed Frobenius pair `(θ, θ^q)`, i.e. a cuspidal label `k` with `θ_k|_{F*_q} = χ_γ`:
   `R_fix((|ns,θ_k⟩ + |ns,θ_k^q⟩)/√2) = |π_{θ_k}⟩`;
3. the antisymmetric combinations are sent to unused labels (vectors supported on `Unused`);
4. for `δ² = γ`: `R_fix|sp, δ⟩ = √((q+1)/(2q))|St_δ⟩ + √((q−1)/(2q))|det_δ⟩` and
   `R_fix|ns, χ_δ ∘ N⟩ = √((q−1)/(2q))|St_δ⟩ − √((q+1)/(2q))|det_δ⟩`;
5. `R_fix` is an isometry.

**Formalization Note** `θ^q` has label `q·k`; `χ_δ ∘ N` has label `(q+1)·δ` in `ZMod (q²−1)`. -/
def IsFixingGate (γ : D.Lab) {U : Type} [Fintype U] (R : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) :
    Prop :=
  (∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}, ab.1.1 + ab.1.2 = γ →
    R.mulVec (isqrt 2 • (eB D γ (.inl ab.1.1) + eB D γ (.inl ab.1.2))) =
      eO D (.inl (.inr (.inr (.inl ab)))) ∧
    ∀ o : D.Irr, R.mulVec (isqrt 2 • (eB D γ (.inl ab.1.1) - eB D γ (.inl ab.1.2))) (.inl o) = 0) ∧
  (∀ k : {k : D.Lab2 // D.IsCuspLabel k}, ∀ (h₁ : D.restrLab k.1 = γ)
      (h₂ : D.restrLab ((D.q : D.Lab2) * k.1) = γ),
    R.mulVec (isqrt 2 • (eB D γ (.inr ⟨k.1, h₁⟩) + eB D γ (.inr ⟨(D.q : D.Lab2) * k.1, h₂⟩))) =
      eO D (.inl (.inr (.inr (.inr k)))) ∧
    ∀ o : D.Irr, R.mulVec (isqrt 2 • (eB D γ (.inr ⟨k.1, h₁⟩) -
      eB D γ (.inr ⟨(D.q : D.Lab2) * k.1, h₂⟩))) (.inl o) = 0) ∧
  (∀ δ : D.Lab, 2 * δ = γ →
    R.mulVec (eB D γ (.inl δ)) =
      ((Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) • eO D (.inl (.inr (.inl δ))) +
        (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) • eO D (.inl (.inl δ))) ∧
    ∀ θ : {θ : D.Lab2 // D.restrLab θ = γ}, θ.1 = (((D.q + 1) * δ.val : ℕ) : D.Lab2) →
      R.mulVec (eB D γ (.inr θ)) =
        ((Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) • eO D (.inl (.inr (.inl δ))) -
          (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) • eO D (.inl (.inl δ)))) ∧
  Rᴴ * R = 1

/-- The block `A_γ` (published `GL2QFT.FieldData.AGamma`, (144)–(145)) with its rows extended by
zero to the unused labels. -/
def AGammaExt (γ : D.Lab) (U : Type) : Matrix (D.Irr ⊕ U) (Option D.Lab) ℂ :=
  Matrix.of fun o c =>
    match o with
    | .inl μ => D.AGamma γ μ c
    | .inr _ => 0

/-- arXiv:2608.28573, Definition 6.21, eqs. (156)–(157), p.50 (PDF p.51): the exceptional
correction `R_exc,γ`: for every `α² = γ` it acts on the ordered pair `(A_γ|c_α⟩, |det_α⟩)` by the
matrix `((−χ_α(−1)/√q, √((q−1)/q)), (√((q−1)/q), χ_α(−1)/√q))`, i.e.
`x A_γ|c_α⟩ + y|det_α⟩ ↦ (m₁₁x + m₁₂y) A_γ|c_α⟩ + (m₂₁x + m₂₂y)|det_α⟩`, and as the identity on the
orthogonal complement. -/
def Rexc (γ : D.Lab) (U : Type) [Fintype U] : Matrix (D.Irr ⊕ U) (D.Irr ⊕ U) ℂ :=
  1 + ∑ α ∈ Finset.univ.filter (fun α : D.Lab => 2 * α = γ),
    let a : D.Irr ⊕ U → ℂ := fun o => AGammaExt D γ U o (some α)
    let d : D.Irr ⊕ U → ℂ := eO D (.inl (.inl α))
    let s : ℂ := D.chi α (-1) / (Real.sqrt D.q : ℂ)
    let c : ℂ := (Real.sqrt (((D.q : ℝ) - 1) / D.q) : ℂ)
    ((-s - 1) • Matrix.vecMulVec a (star a) + c • Matrix.vecMulVec a (star d) +
      c • Matrix.vecMulVec d (star a) + (s - 1) • Matrix.vecMulVec d (star d))

end AGammaGates

end Supplement

end GL2QFT


