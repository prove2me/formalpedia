-- Prove2me | Definitions.Def_EisensteinGeneral_FactorizationDatum
-- name    : EisensteinGeneral_FactorizationDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/a6ee3a2a-b861-5ec0-bdf7-c2b2e2541f2e
-- title:
--   Factorisation data for Eisenstein values on the big cell
-- statement:
--   The module defines a single structure, `FactorizationDatum`, over a number field $F$, with parameters: a family of additive characters $\psi_v$ of the completions $F_v$ at the finite places, an integer-valued function $n\psi$ on the finite places, a character $\chi\colon \mathbb{A}_F^\times \to \mathbb{C}^\times$, a choice of element $\varpi_v \in F_v^\times$ at each finite place, a function $\Psi\colon \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, a point $g \in \mathrm{GL}_2(\mathbb{A}_F)$, and a finite set $S$ of finite places. Its data fields are: exponents $cS_v \in \mathbb{N}$ and a depth $mS \in \mathbb{N}$; a number $n$ of summands; for each $j < n$ local functions $A_j, B_j$ on each $F_v$ and integrands $h_j(v,s,\cdot)$ on $F_v$; archimedean exponent data (an integer $k$ and a real $\tau$ at each real place, a triple $(a,b,m)$ of naturals and a real $\tau$ at each complex place) and the corresponding factors $Wr_j$, $Wc_j$; an idele $a$, an adele $u$, and scalar functions $C_j\colon\mathbb{C}\to\mathbb{C}$.
--
--   The remaining fields are the asserted identities. The localisation of $\chi$ at $v$ (its restriction along the embedding $F_v^\times \hookrightarrow \mathbb{A}_F^\times$) has absolute value $1$ at $\varpi_v$, is trivial on all units of valuation $1$ for $v \notin S$, and is trivial on $\{u : |u|_v = 1,\ |u-1|_v \le q_v^{-cS_v}\}$ for $v \in S$, where $cS_v \ge 1$; also $n\psi_v = 0$ off $S$ and $mS \ge 1$. For $v \in S$, $A_j$ is constant on cosets of depth $mS$ inside $\mathcal{O}_v$ and $B_j$ is constant on such cosets throughout $F_v$. Off $S$, $h_j(v,s,\cdot)$ is $1$ on $\mathcal{O}_v$ and $\chi_v^{-1}(y)\,|y|_v^{-(2s+1)}$ outside it; on $S$ it is $A_j$ on $\mathcal{O}_v$ and $\chi_v^{-1}(y)\,|y|_v^{-(2s+1)}B_j(y^{-1})$ outside, where $\chi_v^{-1}$ is extended by $0$ at the origin and $|\cdot|_v$ is the Haar module. At complex places $a+b \le m$, and the archimedean factors are given by the closed formulas $Wr_j(s,x) = ((x-i)/\sqrt{1+x^2})^{k}(1+x^2)^{-(s+1/2+i\tau/2)}$ and $Wc_j(s,z) = z^{a}\bar z^{b}(1+|z|^2)^{-(2s+1+m/2+i\tau/2)}$. Each $C_j$ is entire, and finally, for all $s$ and all adeles $y$,
--   $$\Psi\bigl(s, w\,u(y)\,g\bigr) = \sum_{j} C_j(s)\prod_{\text{real }i} Wr_j(i,s,x_i)\prod_{\text{complex }w} Wc_j(w,s,z_w)\prod_{v} h_j(v,s,(a(y+u))_v),$$
--   where $w$ is the global Weyl element `adelicWeyl` given by $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $u(y)$ is the unipotent element `unipotentGL2 y`, the archimedean arguments are the components of the mixed-space image of the infinite part of $a\cdot(y+u)$, and the product over finite places is a finprod. A term of the structure is thus exactly such a collection of data together with proofs of these identities; nothing beyond them is asserted.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the height-one spectrum and completions, the mixed-space description of the infinite adeles and the Haar distribution character used for the local modulus, but has no notion of Eisenstein series or of Whittaker-type local factors; this structure, and the auxiliary notions it invokes (`localChar`, `higherUnitsAt`, `charExt`, `modulus`, `adelicWeyl`), are the project's own.
--
--   **Where it is used.** The datum records, for one term of an Eisenstein family evaluated on the big Bruhat cell $w\,U(\mathbb{A}_F)\,g$, a complete factorisation into one factor per place, with explicit archimedean factors and Tate-type local integrands that are standard outside a finite set $S$. It is the bookkeeping device for the constant-term and Weyl-intertwining computations in the automorphic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_EisensteinGeneral_FactorizationDatum.lean

import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

namespace EisensteinGeneral.Piece

open scoped Classical in

structure FactorizationDatum (F : Type) [Field F] [NumberField F]
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) where
  cS : HeightOneSpectrum (𝓞 F) → ℕ
  mS : ℕ
  n : ℕ
  A : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ
  B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ
  h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ
  kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ
  τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ
  abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ
  τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ
  Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ
  Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ
  a : (AdeleRing (𝓞 F) F)ˣ
  u : AdeleRing (𝓞 F) F
  C : Fin n → ℂ → ℂ
  hχϖ : ∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1
  hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
      NumberField.TateGlobal.localChar χ v u = 1
  hnψ : ∀ v ∉ S, nψ v = 0
  hcS : ∀ v ∈ S, 1 ≤ cS v
  hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
      NumberField.TateGlobal.localChar χ v u = 1
  hmS : 1 ≤ mS
  hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x
  hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x
  hoff : ∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x
  hon : ∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
      h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x
  habm : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2
  hWr : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2))
  hWc : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2))
  hC : ∀ j, Differentiable ℂ (C j)
  hfac : ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
      Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
          * (∏ i : {w : InfinitePlace F // w.IsReal},
              Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
          * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v)

end EisensteinGeneral.Piece


