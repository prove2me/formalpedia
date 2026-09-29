-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
-- name    : LanglandsTunnell_CubicInduction_MirabolicMajorant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/29b7c438-2544-572a-9184-186b25cb35f8
-- title:
--   Root sizes and gauge majorants for adelic GL3​
-- statement:
--   Over a normed field $L$, six sizes are attached to $k \in \mathrm{GL}_3(L)$ (rows and columns indexed by $\{0,1,2\}$): `lastRowSup` is the maximum of $\|k_{2j}\|$ for $j=0,1,2$; `bottomMinor k j j'` is the $2\times 2$ minor $k_{1j}k_{2j'}-k_{1j'}k_{2j}$ formed from the last two rows and the columns $j,j'$; `minorSup` is the maximum of the norms of the three minors with $(j,j')=(0,1),(0,2),(1,2)$; `lastRowEucl` and `minorEucl` are the corresponding Euclidean ($\ell^2$) sizes, i.e. the square roots of the sums of the squares of the same three norms; and `detSize` is $\|\det k\|$. For a number field $F$ and $g \in \mathrm{GL}_3(\mathbf{A}_F)$, two root sizes are formed at each place from the local component of $g$: at a finite place $v$, $\mathrm{finRoot}_1 = d\cdot r/m^2$ and $\mathrm{finRoot}_2 = m/r^2$ with $d,r,m$ the determinant size, last-row sup-size and minor sup-size of the component at $v$; at an infinite place $w$ the same formulas with the Euclidean sizes of the component at $w$. Division here follows the Lean convention (quotients by $0$ are $0$); no nondegeneracy is imposed. `rootSizeProd` multiplies the `finprod` over all finite places of $\mathrm{finRoot}_1\cdot\mathrm{finRoot}_2$ by the finite product of $\mathrm{archRoot}_1\cdot\mathrm{archRoot}_2$ over infinite places, and `archRootSum` sums $\mathrm{archRoot}_1+\mathrm{archRoot}_2$ over infinite places. `InRootLevel T B g` asks that both finite root sizes be $\le 1$ at every finite place outside a finite set $T$ and $\le B$ at places of $T$. Finally `IsGaugeMajorised3 W`, for $W : \mathrm{GL}_3(\mathbf{A}_F) \to \mathbb{C}$, asserts the existence of $t \in \mathbb{N}$, a finite set $T$ of finite places and $B \in \mathbb{R}$ such that for every $N \in \mathbb{N}$ there is $C \in \mathbb{R}$ with: $W(g)=0$ whenever `InRootLevel` fails, and $\|W(g)\| \le C/(\mathrm{rootSizeProd}(g)^t (1+\mathrm{archRootSum}(g))^N)$ whenever it holds. The accompanying lemma records that the zero function is gauge-majorised (with $t=0$, $T=\emptyset$, $B=1$, $C=0$).
--
--   **Relation to Mathlib.** Mathlib supplies the ambient objects (the adele ring, the height-one spectrum, infinite places and their completions, and `finprod`) but has no notion of these root sizes or of gauge majorisation; both are the project's own.
--
--   **Where it is used.** These sizes implement the two simple roots of $\mathrm{GL}_3$ in matrix terms, and the majorisation predicate is the decay condition imposed on Whittaker-type functions in the $\mathrm{GL}_3$ induction step used for the Langlands–Tunnell theorem, which supplies modularity of the mod $3$ representation in the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_MirabolicMajorant.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Growth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Sizes

variable {L : Type*} [NormedField L]

def lastRowSup (k : GL (Fin 3) L) : ℝ :=
  max (max ‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖)
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖

def bottomMinor (k : GL (Fin 3) L) (j j' : Fin 3) : L :=
  (k : Matrix (Fin 3) (Fin 3) L) 1 j * (k : Matrix (Fin 3) (Fin 3) L) 2 j' -
    (k : Matrix (Fin 3) (Fin 3) L) 1 j' * (k : Matrix (Fin 3) (Fin 3) L) 2 j

def minorSup (k : GL (Fin 3) L) : ℝ :=
  max (max ‖bottomMinor k 0 1‖ ‖bottomMinor k 0 2‖) ‖bottomMinor k 1 2‖

def lastRowEucl (k : GL (Fin 3) L) : ℝ :=
  Real.sqrt (‖(k : Matrix (Fin 3) (Fin 3) L) 2 0‖ ^ 2 + ‖(k : Matrix (Fin 3) (Fin 3) L) 2 1‖ ^ 2 +
    ‖(k : Matrix (Fin 3) (Fin 3) L) 2 2‖ ^ 2)

def minorEucl (k : GL (Fin 3) L) : ℝ :=
  Real.sqrt (‖bottomMinor k 0 1‖ ^ 2 + ‖bottomMinor k 0 2‖ ^ 2 + ‖bottomMinor k 1 2‖ ^ 2)

def detSize (k : GL (Fin 3) L) : ℝ :=
  ‖(k : Matrix (Fin 3) (Fin 3) L).det‖

end Sizes

section Roots

variable (F : Type) [Field F] [NumberField F]

def finRoot₁ (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  detSize (componentAt3 (𝓞 F) F v g) * lastRowSup (componentAt3 (𝓞 F) F v g) /
    minorSup (componentAt3 (𝓞 F) F v g) ^ 2

def finRoot₂ (v : HeightOneSpectrum (𝓞 F)) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  minorSup (componentAt3 (𝓞 F) F v g) / lastRowSup (componentAt3 (𝓞 F) F v g) ^ 2

def archRoot₁ (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  detSize (archPlaceComponent3 F w g) * lastRowEucl (archPlaceComponent3 F w g) /
    minorEucl (archPlaceComponent3 F w g) ^ 2

def archRoot₂ (w : InfinitePlace F) (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  minorEucl (archPlaceComponent3 F w g) / lastRowEucl (archPlaceComponent3 F w g) ^ 2

def rootSizeProd (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  (∏ᶠ v : HeightOneSpectrum (𝓞 F), finRoot₁ F v g * finRoot₂ F v g) *
    ∏ w : InfinitePlace F, archRoot₁ F w g * archRoot₂ F w g

def archRootSum (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  ∑ w : InfinitePlace F, (archRoot₁ F w g + archRoot₂ F w g)

def InRootLevel (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ) (g : AdelicGL 3 (𝓞 F) F) : Prop :=
  (∀ v, v ∉ T → finRoot₁ F v g ≤ 1 ∧ finRoot₂ F v g ≤ 1) ∧
    ∀ v ∈ T, finRoot₁ F v g ≤ B ∧ finRoot₂ F v g ≤ B

def IsGaugeMajorised3 (W : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  ∃ (t : ℕ) (T : Finset (HeightOneSpectrum (𝓞 F))) (B : ℝ), ∀ N : ℕ, ∃ C : ℝ,
    ∀ g : AdelicGL 3 (𝓞 F) F,
      (¬ InRootLevel F T B g → W g = 0) ∧
        (InRootLevel F T B g → ‖W g‖ ≤ C / (rootSizeProd F g ^ t * (1 + archRootSum F g) ^ N))

theorem isGaugeMajorised3_zero : IsGaugeMajorised3 F (fun _ => (0 : ℂ)) :=
  ⟨0, ∅, 1, fun N => ⟨0, fun g => ⟨fun _ => rfl, fun _ => by simp⟩⟩⟩

end Roots

end LanglandsTunnell.CubicInduction


