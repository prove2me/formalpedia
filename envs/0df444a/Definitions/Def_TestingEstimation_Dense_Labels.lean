-- Prove2me | Definitions.Def_TestingEstimation_Dense_Labels
-- name    : TestingEstimation_Dense_Labels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:27.763376+00:00
-- url     : https://prove2.me/theorems/a61f6045-027c-43d5-acac-bcfc2f64b158
-- title:
--   Tester derivatives, all pair tests, and the finite label decoder
-- statement:
--   Write $s=a+2$, so the $a$ anchors are the sample positions other than the first two. For an anchor graph $b$, two Boolean anchor vectors $x,y$, and a bit $t$, the graph $F_t(b,x,y)$ has endpoint edge $t$, endpoint-to-anchor vectors $x,y$, and anchor graph $b$. Define
--
--   $$\partial_b f(x,y)=f(F_1(b,x,y))-f(F_0(b,x,y)).$$
--
--   A color belongs to $\Omega=\{\bot\}\sqcup(\{0,1\}^a\times\{0,1\}^a)$. The symmetric kernel is zero if either color is bottom, and otherwise
--
--   $$\kappa_b((x,y),(x',y'))=\tfrac12\bigl(\partial_b f(x,y')+\partial_b f(x',y)\bigr).$$
--
--   For every anchor graph $b$ and every coloring $\chi$ of the whole vertex set, include the pair function $A_{b,\chi}(uv)=\kappa_b(\chi(u),\chi(v))$. The finite test family $T(G)$ contains all these functions and the cost test $1-2G$. Colorings are unrestricted.
--
--   Fix real $0<\gamma<1$ and let $L=\lceil\gamma^{-2}\rceil$. A common symbol is empty, a signed cost symbol, or a signed derivative symbol with an anchor graph. A label in $\Lambda=(C\times\Omega)^L$ stores a common symbol and a local color at each slot. The decoder $D(g,z,z')$ returns the original bit $g$ if common symbols disagree in any slot. Otherwise it returns
--
--   $$\operatorname{clip}\left(g+\gamma\sum_{\ell=1}^L\mu_\ell\right),$$
--
--   where $\mu_\ell$ is zero for an empty symbol, $\sigma(1-2g)$ for a signed cost symbol, and $\sigma\kappa_b(\omega_\ell,\omega'_\ell)$ for a signed derivative symbol. Every labeling, consistent or inconsistent, defines $W_z(uv)=D(G(uv),z_u,z_v)$. Define $\widetilde M(G)=\inf_z E_G(W_z)$ over all labelings. These finite labels have no dependence on the input order.
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Definitions 1–2 and §§4.1–4.2, pp. 10–11, 14–15 (PDF pages equal printed pages)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense
attribute [local instance] Classical.propDecidable

/-- In this module the canonical sample has a+2 vertices and a anchors. -/
def anchorIndex {a : ℕ} (i : Fin (a+2)) (h : 2 ≤ i.val) : Fin a :=
  ⟨i.val-2, by omega⟩

def gadget {a : ℕ} (t : Bool) (b : Graph a) (x y : Fin a → Bool) : Graph (a+2) := by
  intro e
  have hab : e.val.1.val < e.val.2.val := e.property
  by_cases h0 : e.val.1.val = 0
  · by_cases h1 : e.val.2.val = 1
    · exact t
    · exact x (anchorIndex e.val.2 (by omega))
  · by_cases h1 : e.val.1.val = 1
    · exact y (anchorIndex e.val.2 (by omega))
    · exact b ⟨(anchorIndex e.val.1 (by omega), anchorIndex e.val.2 (by omega)), by
        change e.val.1.val - 2 < e.val.2.val - 2
        omega⟩

def derivative {a : ℕ} (f : Rule (a+2)) (b : Graph a) (x y : Fin a → Bool) : ℝ :=
  ruleValue f (gadget true b x y) - ruleValue f (gadget false b x y)

abbrev Color (a : ℕ) := Option ((Fin a → Bool) × (Fin a → Bool))

def kernel {a : ℕ} (f : Rule (a+2)) (b : Graph a) : Color a → Color a → ℝ
  | some (x,y), some (x',y') => (derivative f b x y' + derivative f b x' y) / 2
  | _, _ => 0

def derivativeTest {a n : ℕ} (f : Rule (a+2)) (b : Graph a) (χ : Fin n → Color a) : PairFunction n :=
  fun e => kernel f b (χ e.val.1) (χ e.val.2)

def tests {a n : ℕ} (f : Rule (a+2)) (G : Graph n) : Finset (PairFunction n) :=
  {fun e => 1 - 2 * bit (G e)} ∪
    Finset.univ.image (fun p : Graph a × (Fin n → Color a) => derivativeTest f p.1 p.2)

/-- empty, signed cost, or signed derivative with its anchor graph. -/
abbrev Symbol (a : ℕ) := Unit ⊕ (Bool ⊕ (Bool × Graph a))
abbrev Label (a : ℕ) (γ : ℝ) := Fin (⌈(γ^2)⁻¹⌉₊) → Symbol a × Color a

def increment {a : ℕ} (f : Rule (a+2)) (g : Bool) (c : Symbol a) (ω ω' : Color a) : ℝ :=
  match c with
  | .inl _ => 0
  | .inr (.inl σ) => sign σ * (1 - 2 * bit g)
  | .inr (.inr (σ,b)) => sign σ * kernel f b ω ω'

def decoder {a : ℕ} (f : Rule (a+2)) (γ : ℝ) (g : Bool)
    (z z' : Label a γ) : UnitWeight :=
  if ∃ l, (z l).1 ≠ (z' l).1 then
    if g then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩
  else clip (bit g + γ * ∑ l, increment f g (z l).1 (z l).2 (z' l).2)

def decoded {a n : ℕ} (f : Rule (a+2)) (γ : ℝ) (G : Graph n)
    (z : Fin n → Label a γ) : WGraph n :=
  fun e => decoder f γ (G e) (z e.val.1) (z e.val.2)

def labelMinimum {a n : ℕ} (f : Rule (a+2)) (γ : ℝ) (G : Graph n) : ℝ :=
  sInf (Set.range (fun z : Fin n → Label a γ => energy f G (decoded f γ G z)))

end TestingEstimation.Dense


