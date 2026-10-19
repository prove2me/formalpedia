-- Prove2me | Definitions.Def_ArtinGLWeight
-- name    : ArtinGLWeight
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T10:52:25.317711+00:00
-- url     : https://prove2.me/theorems/d6c9ab68-6fbc-4078-a29c-cb33003b84e1
-- title:
--   The smooth weight, its Mellin transform and the terms of Goldmakher–Louvel's explicit formula for Σ₃, for the exterior quadratic symbols of OpenAI's Primitive roots paper
-- statement:
--   Objects for §§5–7 of L. Goldmakher and B. Louvel, *A quadratic large sieve inequality over number fields*, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, for the family of Lemma 6.4 of OpenAI, *Primitive roots for every admissible integer base* (2026), p. 38. They are built on the bundle `Def_ArtinHeckeTheta` (`IsExterior`, `AllowedGen`, `residueSymbol`), in the namespace `ArtinPrimitiveRoots.GLW`. Here $F$ is a number field, $q_I$ is the absolute norm of an ideal $I$ of $\mathcal O_F$, $r_2$ is the number of complex places of $F$, $d_F$ is the discriminant, and $\mathfrak m, \mathfrak g, \mathfrak c$ are ideals of $\mathcal O_F$.
--
--   - `WB`: the smooth bump function (`ContDiffBump`) centred at $3/2$ with inner radius $1/2$ and outer radius $1$. `W t` is its value at $t$: $0 \le W \le 1$, $W = 1$ on $[1, 2]$, and $W = 0$ outside $(1/2, 5/2)$. `Wm s` $= \int_0^\infty W(t)\,t^{s-1}\,dt$ (`mellin`).
--   - `R0 F`: a function $R$ with $R$ entire, $R(s) = (s-1)\zeta_F(s)$ for $\operatorname{Re} s > 1$, $R(1)$ = `dedekindZeta_residue F`, and, for every $X$, $|R(s)| \le C(1 + |\operatorname{Im} s|)^A$ on $-1/2 \le \operatorname{Re} s \le X$ for some $C, A \ge 0$. It is chosen with `Classical.epsilon`, so it is such a function whenever one exists.
--   - `primesOf 𝔤`: the set of prime ideals dividing $\mathfrak g$, the distinct elements of `normalizedFactors 𝔤`. `pideal f` $= \prod_{P \in f} P$.
--   - `sqfRows 𝔪 Y`: the finite set of ideals $\mathfrak a$ that are exterior to $\mathfrak m$, squarefree, with $q_{\mathfrak a} \le Y$. `Srow 𝔪 𝔤 L`: those of `sqfRows 𝔪 L` coprime to $\mathfrak g$ ($\mathfrak a + \mathfrak g = \mathcal O_F$).
--   - `sgt L 𝔞`: $L\,q_{\mathfrak b}^2 < q_{\mathfrak a}$ for every ideal $\mathfrak b$ with $\mathfrak b^2 \mid \mathfrak a$ (the squarefree part of $\mathfrak a$ has norm $> L$).
--   - `PsiHyp 𝔪 c ψ`, for $\psi$ a complex function on ideals: $\psi(IJ) = \psi(I)\psi(J)$ for nonzero $I, J$; $|\psi| \le 1$; $\psi(I) = 0$ for nonzero $I$ not coprime to $\mathfrak m$; for nonzero $r$ coprime to $\mathfrak m$, $\psi(r)^2$ is $1$ if $r$ is coprime to $\mathfrak c$ and $0$ otherwise; $\psi(\mathcal O_F) = 1$.
--   - `Dc c` $= |d_F|\,q_{\mathfrak c}$, as a complex number.
--   - `LamHyp 𝔪 c ψ Λ`: $\Lambda$ is entire; $\Lambda(w) = \prod_{P \in \texttt{primesOf } \mathfrak m}(1 - q_P^{-w})^{-1}\sum_{\mathfrak a}\psi(\mathfrak a)q_{\mathfrak a}^{-w}$ for $\operatorname{Re} w > 1$; $D^{w/2}\Gamma_{\mathbb C}(w)^{r_2}\Lambda(w) = D^{(1-w)/2}\Gamma_{\mathbb C}(1-w)^{r_2}\Lambda(1-w)$ with $D$ = `Dc c`, whenever neither $w$ nor $1 - w$ is in $\{0, -1, -2, \dots\}$; and on every vertical strip $|\Lambda(w)| \le C(1 + |\operatorname{Im} w|)^A$ for some $C, A$.
--   - `Em 𝔪 𝔤 ψ w` $= \prod_{P \mid \mathfrak m}(1 - q_P^{-w})\prod_{P \mid \mathfrak g}(1 - \psi(P)q_P^{-w})$. `Zm 𝔪 u` $= \prod_{P \mid \mathfrak m}(1 - q_P^{-u})^{-1}$. Here $P \mid \mathfrak m$ means $P \in$ `primesOf 𝔪`.
--   - `G0 w` $= (2\pi)^{2w-1}\Gamma(1-w)^2\sin(\pi w)/\pi$.
--   - `Kd 𝔪 𝔤 c ψ M w` $= M^w\,$`Em 𝔪 𝔤 ψ w`$\,D^{1/2-w}\,$`G0 w`$^{r_2}\,$`Zm 𝔪 (1 - w)`$\,\prod_{P \mid \mathfrak m\mathfrak c}(1 - q_P^{-2(1-w)})$, with $D$ = `Dc c`.
--   - `Pf 𝔪 ψ L' u` $= \sum_{s \in \texttt{sqfRows } \mathfrak m\ L'}\psi(s)q_s^{-u}$. `Qf ψ L' u` $= \sum_{s}\psi(s)q_s^{-u}$ over the nonzero squarefree $s$ with $q_s > L'$ (a `tsum`).
--   - `HP 𝔪 𝔤 c ψ M L' w` $=$ `Kd`$\,\cdot\,$`R0 F (2(1 - w))`$/(1 - 2w)\,\cdot\,$`Pf 𝔪 ψ L' (1 - w)`. `HQ 𝔪 𝔤 c ψ M L' w` $=$ `Kd`$\,\cdot\,\zeta_F(2(1-w))\,\cdot\,$`Qf ψ L' (1 - w)`.
--   - `RPt 𝔪 𝔤 c ψ M L ε` $= \sum_{s \in \texttt{Srow } \mathfrak m\,\mathfrak g\,L}\psi(s)\,\frac{1}{2\pi}\int_{\mathbb R}$`Wm`$(w)\,(q_s/M)^{-w}\prod_{P \mid \mathfrak g\mathfrak m\mathfrak c}(1 - q_P^{-2w})\,$`R0 F (2w)`$/(2w - 1)\,dt$, with $w = \varepsilon + it$.
--   - `TTt 𝔪 𝔤 c ψ M L L'` $=$ `R0 F 1`$/2\cdot M^{1/2}\,$`Wm (1/2)`$\prod_{P \mid \mathfrak m\mathfrak c}(1 - q_P^{-1})\sum_{e, f \subseteq \texttt{primesOf } \mathfrak g}(-1)^{|e|}\psi(\mathfrak p_e)q_{\mathfrak p_e}^{-1/2}\psi(\mathfrak p_f)q_{\mathfrak p_f}^{-1/2}\Big(\sum_{s \in \texttt{Srow } \mathfrak m\,\mathfrak g\,(L'/q_{\mathfrak p_f})}\psi(s)q_s^{-1/2} - \sum_{s \in \texttt{Srow } \mathfrak m\,\mathfrak g\,L}\psi(s)q_s^{-1/2}\Big)$, with $\mathfrak p_e$ = `pideal e`.
--   - `DPt 𝔪 𝔤 c ψ M L' ε'` $= \frac{1}{2\pi}\int_{\mathbb R}$`Wm`$(w)\,$`HP`$(w)\,dt$ with $w = 1 - \varepsilon' + it$. `DQt 𝔪 𝔤 c ψ M L' σ₁` $= \frac{1}{2\pi}\int_{\mathbb R}$`Wm`$(w)\,$`HQ`$(w)\,dt$ with $w = -\sigma_1 + it$.
--   - `psiP g c₁ c₂` is the function $\mathfrak a \mapsto \chi_{\mathfrak c_1}(\mathfrak a)\chi_{\mathfrak c_2}(\mathfrak a)$, where $\chi_{\mathfrak c}(\mathfrak a)$ = `residueSymbol ι 𝔪 𝔞 (g.gen 𝔠) ^ 3`.
--   - `PSnp C z G` $= \sum_{\mathfrak c_1, \mathfrak c_2 \in C} z(\mathfrak c_1)\overline{z(\mathfrak c_2)}\,G(\mathfrak c_1, \mathfrak c_2)$ over the pairs with $\mathfrak c_1 + \mathfrak c_2 = \mathcal O_F$, leaving out $\mathfrak c_1 = \mathfrak c_2 = \mathcal O_F$. `Ztau C z` $= \sum_{\mathfrak c \in C} 8^{\omega(\mathfrak c)}|z(\mathfrak c)|^2$, with $\omega(\mathfrak c)$ the number of prime factors of $\mathfrak c$.
--   - `sbBound ι 𝔪 g R C v`: $\sum_{\mathfrak a \in R}\big|\sum_{\mathfrak c \in C} z(\mathfrak c)\chi_{\mathfrak c}(\mathfrak a)\big|^2 \le v\sum_{\mathfrak c \in C}|z(\mathfrak c)|^2$ for every complex function $z$.
--   - `nblk Y₀ Y₁` $= \lceil \log_2 \lceil Y_1/Y_0\rceil\rceil$ (`Nat.clog 2 ⌈Y₁ / Y₀⌉₊`), the number of dyadic blocks from $Y_0$ to $Y_1$.
--
--   In Goldmakher–Louvel's notation, $W$ is their smooth weight $h$ and `Wm` its Mellin transform $\hat h$. `psiP g c₁ c₂` is $\chi_{\mathfrak b_1}\chi_{\mathfrak b_2}$ after the common factor $\mathfrak g$ of their $\Sigma_3$ is removed. `TTt`, `DPt`, `DQt` and `RPt` are the four terms of the explicit formula for the row sum of one pair; `PSnp` is the sum of a pair term over the pairs of columns with greatest common divisor $\mathcal O_F$; and `sbBound` is their bilinear-form bound $B_2$ for a finite set of rows.
--
--   **Formalization note.** The explicit formula here is our own route through the functional equation of `LamHyp` rather than Goldmakher–Louvel's (E1)–(E5): the dual sum is split at $L'$ into `Pf` and `Qf`, and the main terms are combined into `TTt`. `R0 F` is a `Classical.epsilon` choice.
-- source:
--   L. Goldmakher and B. Louvel, A quadratic large sieve inequality over number fields, Math. Proc. Cambridge Philos. Soc. 154 (2013), no. 2, 193–212, https://doi.org/10.1017/S0305004112000370, p. 193–212, §§5–7 (the smooth weight W and its Mellin transform, (s − 1)ζ_F, the pair characters and the terms T − T′, DP, DQ, RP of the explicit formula for Σ₃, and the bilinear sums over coprime pairs)

import Mathlib
import Definitions.Def_ArtinHeckeTheta

namespace ArtinPrimitiveRoots.GLW

open NumberField Complex MeasureTheory UniqueFactorizationMonoid
open scoped Real

variable {F : Type*} [Field F] [NumberField F]

noncomputable def WB : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

noncomputable def W (t : ℝ) : ℝ := WB t

noncomputable def Wm (s : ℂ) : ℂ := mellin (fun t : ℝ => (W t : ℂ)) s

variable (F) in
noncomputable def R0 : ℂ → ℂ :=
  Classical.epsilon fun R : ℂ → ℂ => Differentiable ℂ R ∧
    (∀ s : ℂ, 1 < s.re → R s = (s - 1) * dedekindZeta F s) ∧
    R 1 = (dedekindZeta_residue F : ℂ) ∧
    ∀ X : ℝ, ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ X →
      ‖R s‖ ≤ C * (1 + |s.im|) ^ A

noncomputable def primesOf (𝔤 : Ideal (𝓞 F)) : Finset (Ideal (𝓞 F)) :=
  haveI := Classical.decEq (Ideal (𝓞 F)); (normalizedFactors 𝔤).toFinset

noncomputable def pideal (f : Finset (Ideal (𝓞 F))) : Ideal (𝓞 F) := ∏ P ∈ f, P

noncomputable def sqfRows (𝔪 : Ideal (𝓞 F)) (Y : ℝ) : Finset (Ideal (𝓞 F)) :=
  (Set.Finite.subset (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊Y⌋₊)
    (fun a (h : a ∈ {a : Ideal (𝓞 F) | IsExterior 𝔪 a ∧ Squarefree a ∧
      (Ideal.absNorm a : ℝ) ≤ Y}) => Nat.le_floor h.2.2)).toFinset

noncomputable def Srow (𝔪 𝔤 : Ideal (𝓞 F)) (L : ℝ) : Finset (Ideal (𝓞 F)) :=
  haveI := Classical.decEq (Ideal (𝓞 F)); (sqfRows 𝔪 L).filter (fun s => s ⊔ 𝔤 = ⊤)

def sgt (L : ℝ) (a : Ideal (𝓞 F)) : Prop :=
  ∀ b : Ideal (𝓞 F), b ^ 2 ∣ a → L * (Ideal.absNorm b : ℝ) ^ 2 < Ideal.absNorm a

structure PsiHyp (𝔪 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) : Prop where
  mul : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → ψ (I * J) = ψ I * ψ J
  norm_le : ∀ I, ‖ψ I‖ ≤ 1
  nonext : ∀ I, I ≠ ⊥ → I ⊔ 𝔪 ≠ ⊤ → ψ I = 0
  sq : ∀ r, r ≠ ⊥ → r ⊔ 𝔪 = ⊤ → ψ r ^ 2 = if r ⊔ c = ⊤ then 1 else 0
  top : ψ ⊤ = 1

noncomputable def Dc (c : Ideal (𝓞 F)) : ℂ := ((|discr F| : ℤ) : ℂ) * (Ideal.absNorm c : ℂ)

structure LamHyp (𝔪 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (Λ : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ Λ
  dir : ∀ w : ℂ, 1 < w.re → Λ w = (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-w)))⁻¹ *
    ∑' a : Ideal (𝓞 F), ψ a * (Ideal.absNorm a : ℂ) ^ (-w)
  fe : ∀ w : ℂ, (∀ m : ℕ, w ≠ -(m : ℂ)) → (∀ m : ℕ, 1 - w ≠ -(m : ℂ)) →
    Dc c ^ (w / 2) * Gammaℂ w ^ InfinitePlace.nrComplexPlaces F * Λ w =
      Dc c ^ ((1 - w) / 2) * Gammaℂ (1 - w) ^ InfinitePlace.nrComplexPlaces F * Λ (1 - w)
  growth : ∀ σ₁ σ₂ : ℝ, ∃ C A : ℝ, ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖Λ w‖ ≤ C * (1 + |w.im|) ^ A

noncomputable def Em (𝔪 𝔤 : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (w : ℂ) : ℂ :=
  (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-w))) *
    ∏ P ∈ primesOf 𝔤, (1 - ψ P * (Ideal.absNorm P : ℂ) ^ (-w))

noncomputable def Zm (𝔪 : Ideal (𝓞 F)) (u : ℂ) : ℂ :=
  (∏ P ∈ primesOf 𝔪, (1 - (Ideal.absNorm P : ℂ) ^ (-u)))⁻¹

noncomputable def G0 (w : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (2 * w - 1) * Gamma (1 - w) ^ 2 * Complex.sin (π * w) / π

noncomputable def Kd (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M : ℝ) (w : ℂ) : ℂ :=
  (M : ℂ) ^ w * Em 𝔪 𝔤 ψ w * Dc c ^ (1 / 2 - w) * G0 w ^ InfinitePlace.nrComplexPlaces F *
    Zm 𝔪 (1 - w) * ∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * (1 - w))))

noncomputable def Pf (𝔪 : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (L' : ℝ) (u : ℂ) : ℂ :=
  ∑ s ∈ sqfRows 𝔪 L', ψ s * (Ideal.absNorm s : ℂ) ^ (-u)

noncomputable def Qf (ψ : Ideal (𝓞 F) → ℂ) (L' : ℝ) (u : ℂ) : ℂ :=
  ∑' s : {s : Ideal (𝓞 F) // s ≠ ⊥ ∧ Squarefree s},
    if L' < (Ideal.absNorm s.1 : ℝ) then ψ s.1 * (Ideal.absNorm s.1 : ℂ) ^ (-u) else 0

noncomputable def HP (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L' : ℝ) (w : ℂ) : ℂ :=
  Kd 𝔪 𝔤 c ψ M w * (R0 F (2 * (1 - w)) / (1 - 2 * w)) * Pf 𝔪 ψ L' (1 - w)

noncomputable def HQ (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L' : ℝ) (w : ℂ) : ℂ :=
  Kd 𝔪 𝔤 c ψ M w * dedekindZeta F (2 * (1 - w)) * Qf ψ L' (1 - w)

noncomputable def RPt (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L ε : ℝ) : ℂ :=
  ∑ s ∈ Srow 𝔪 𝔤 L, ψ s * ((1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (ε + t * I) *
    ((((Ideal.absNorm s : ℝ) / M : ℝ) : ℂ) ^ (-((ε : ℂ) + t * I)) *
      (∏ P ∈ primesOf (𝔤 * 𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(2 * ((ε : ℂ) + t * I))))) *
      R0 F (2 * ((ε : ℂ) + t * I)) / (2 * ((ε : ℂ) + t * I) - 1)))

noncomputable def TTt (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L L' : ℝ) : ℂ :=
  R0 F 1 / 2 * (M : ℂ) ^ (1 / 2 : ℂ) * Wm (1 / 2) *
    (∏ P ∈ primesOf (𝔪 * c), (1 - (Ideal.absNorm P : ℂ) ^ (-(1 : ℂ)))) *
    ∑ e ∈ (primesOf 𝔤).powerset, ∑ f ∈ (primesOf 𝔤).powerset,
      ((-1 : ℂ) ^ e.card * ψ (pideal e) * (Ideal.absNorm (pideal e) : ℂ) ^ (-(1 / 2 : ℂ)) *
        ψ (pideal f) * (Ideal.absNorm (pideal f) : ℂ) ^ (-(1 / 2 : ℂ))) *
      ((∑ s ∈ Srow 𝔪 𝔤 (L' / Ideal.absNorm (pideal f)),
          ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ))) -
        ∑ s ∈ Srow 𝔪 𝔤 L, ψ s * (Ideal.absNorm s : ℂ) ^ (-(1 / 2 : ℂ)))

noncomputable def DPt (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L' ε' : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (((1 - ε' : ℝ) : ℂ) + t * I) *
    HP 𝔪 𝔤 c ψ M L' (((1 - ε' : ℝ) : ℂ) + t * I)

noncomputable def DQt (𝔪 𝔤 c : Ideal (𝓞 F)) (ψ : Ideal (𝓞 F) → ℂ) (M L' σ₁ : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, Wm (((-σ₁ : ℝ) : ℂ) + t * I) *
    HQ 𝔪 𝔤 c ψ M L' (((-σ₁ : ℝ) : ℂ) + t * I)

noncomputable def psiP {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} (g : AllowedGen ι 𝔪) (c₁ c₂ : Ideal (𝓞 F)) :
    Ideal (𝓞 F) → ℂ :=
  fun a => residueSymbol ι 𝔪 a (g.gen c₁) ^ 3 * residueSymbol ι 𝔪 a (g.gen c₂) ^ 3

open Classical in
noncomputable def PSnp (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ)
    (G : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ) : ℂ :=
  ∑ c₁ ∈ C, ∑ c₂ ∈ C, (if c₁ ⊔ c₂ = ⊤ ∧ ¬ (c₁ = ⊤ ∧ c₂ = ⊤) then
    z c₁ * starRingEnd ℂ (z c₂) * G c₁ c₂ else 0)

noncomputable def Ztau (C : Finset (Ideal (𝓞 F))) (z : Ideal (𝓞 F) → ℂ) : ℝ :=
  ∑ c ∈ C, (8 : ℝ) ^ (primesOf c).card * ‖z c‖ ^ 2

def sbBound (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (g : AllowedGen ι 𝔪) (R C : Finset (Ideal (𝓞 F)))
    (v : ℝ) : Prop :=
  ∀ z : Ideal (𝓞 F) → ℂ, ∑ a ∈ R, ‖∑ c ∈ C, z c * residueSymbol ι 𝔪 a (g.gen c) ^ 3‖ ^ 2 ≤
    v * ∑ c ∈ C, ‖z c‖ ^ 2

noncomputable def nblk (Y₀ Y₁ : ℝ) : ℕ := Nat.clog 2 ⌈Y₁ / Y₀⌉₊

end ArtinPrimitiveRoots.GLW


