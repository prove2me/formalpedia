-- Prove2me | Definitions.Def_RandomIsetThreshold_Degree_SelectorFourier
-- name    : RandomIsetThreshold_Degree_SelectorFourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:10:48.840694+00:00
-- url     : https://prove2.me/theorems/fa0d0c20-e5d9-41ca-823a-fa19b447dcf7
-- title:
--   Lexicographic independent-set selector and its biased Fourier projection
-- statement:
--   Order vertex subsets by their increasing vertex lists, using the usual lexicographic order with a shorter prefix first. Let $\mathcal L_k(G)$ be the first independent $k$-set, or the empty set when none exists, and set $h(G)=1_{\mathcal L_k(G)}$. For $0<p<1$, put
--
--   $$\chi_F(G)=\prod_{e\in F}\frac{G_e-p}{\sqrt{p(1-p)}},\qquad \widehat h(F)=\mathbb E[h(H_{n,p})\chi_F(H_{n,p})],\qquad h_{\le D}(G)=\sum_{|F|\le D}\widehat h(F)\chi_F(G).$$
--
--   The selector is determined from the actual hypergraph, without an independent-set oracle. The Fourier definitions are coordinatewise wrappers around the published scalar biased Fourier basis and projection. Their weights are exactly the Bernoulli product weights of the hypergraph law.
--
--   These are the specific witnesses in Theorem 2.1. **Formalization Note** Lexicographic selection minimizes an injective base-$n+1$ code of the increasing list with zero padding; real vertex labels are shifted by one in that code so zero is a terminator. This also defines the empty-case behavior.
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 7–8, §§2.1–2.2, equations (14)–(17)

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_RandomOutput
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection

namespace RandomIsetThreshold.Degree

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

variable {n r : ℕ}

/-- Base n+1 code of the increasing vertex list, padded by zero; smaller codes are
lexicographically earlier. Vertex v is encoded as v+1, so the zero terminator comes first. -/
def lexCode (I : Finset (Fin n)) : ℕ :=
  ∑ i ∈ Finset.range n,
    (if i < I.card then ((I.sort (· ≤ ·)).map (fun v => v.val + 1)).getD i 0 else 0) *
      (n + 1) ^ (n - 1 - i)

/-- The minimum lexicographic code among the actual candidates; empty on failure. -/
def lexFirst (P : Finset (Fin n) → Prop) : Finset (Fin n) := by
  classical
  let candidates := Finset.univ.filter P
  exact if h : candidates.Nonempty then
    Classical.choose (Finset.mem_image.mp
      (Finset.min'_mem (candidates.image lexCode) (h.image lexCode)))
  else ∅

def lexIndependent (k : ℕ) (G : Cube n r) : Finset (Fin n) :=
  lexFirst (fun I => I.card = k ∧ Independent G I)

def selector (k : ℕ) (G : Cube n r) : Vector n := indicator (lexIndependent k G)

def character (p : unitInterval) (F : Finset (Edge n r)) (G : Cube n r) : ℝ :=
  OAI.Problem313.BiasedFourier.char (p : ℝ) F G

/-- Coordinatewise wrapper around the published biased Fourier coefficient. -/
def fourierCoefficient (p : unitInterval) (h : Cube n r → Vector n)
    (F : Finset (Edge n r)) : Vector n :=
  fun v => OAI.Problem313.BiasedFourier.coeff (p : ℝ) (fun G => h G v) F

/-- Coordinatewise low-degree projection using the published scalar projection. -/
def fourierProjection (p : unitInterval) (D : ℕ)
    (h : Cube n r → Vector n) (G : Cube n r) : Vector n := by
  classical
  exact fun v => OAI.Problem313.BiasedFourier.project (p : ℝ)
    (Finset.univ.filter (fun F : Finset (Edge n r) => F.card ≤ D)) (fun H => h H v) G

end
end RandomIsetThreshold.Degree


