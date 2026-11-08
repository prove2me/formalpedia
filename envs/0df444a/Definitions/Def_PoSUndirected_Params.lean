-- Prove2me | Definitions.Def_PoSUndirected_Params
-- name    : PoSUndirected_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:52.864917+00:00
-- url     : https://prove2.me/theorems/c335c5b6-f1a3-4763-92c5-6107f6e0196d
-- title:
--   The parameter segment $\eta(t)=(1-t)\eta_0+t\eta_1$ of the lower construction and its totals
-- statement:
--   A parameter vector $\eta$ consists of twenty rationals: the nominal floor costs $a,\dots,k$, the effective chord coordinates $x,y,z,u,v,w$, a parameter $\alpha$, and the pendant costs $L_y,L_z$. The physical chord costs are $x,\;y-L_y,\;z-L_z,\;u,\;v,\;w$. Its totals are
--   $$
--   S=a+\dots+k+L_y+L_z,\quad C_\Sigma=x+y+z+u+v+w-L_y-L_z,\quad S_{\rm rec}=a+b+j+k+L_y+L_z,
--   $$
--   $$
--   U_{\rm fix}=S-S_{\rm rec},\qquad B_{\rm rec}=S_{\rm rec}/\alpha,\qquad \mathcal L(\eta)=\frac{S+C_\Sigma}{S-\alpha}.
--   $$
--   The two endpoint vectors $\eta_0,\eta_1$ are given by the integer table of Appendix A.5 over the common denominators $D_0'=33964062239365007131388227765376$ and $D_1'=6391299264938$, and the construction uses $\eta(t)=(1-t)\eta_0+t\eta_1$ for rational $0\le t<1$. The constant of the main theorem is
--   $$
--   L=\frac{7808358178989}{3195649632469}=2.44343375433\ldots
--   $$
--
--   These numbers fix the gadget of the lower bound; $\mathcal L(\eta(t))$ increases to $L$ as $t\to1$.
--
--   **Formalization Note** $\mathcal L(\eta)$ (`Params.Leta`) and the constant $L$ (`Lconst`) are different objects, as in the paper. At $\eta_1$ the pendant cost $L_y$ is $0$, so $\eta_1$ is never used as a game.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §3, p.4 (PDF p.6); §A.4, p.18 (PDF p.20); §A.5 table, pp.18–19 (PDF pp.20–21)

import Mathlib

namespace PoSUndirected

/-- A parameter vector `η` of the lower construction (Tsoufis, preprint, sha256 c095d811…, §3,
p.4 (PDF p.6) and §A.5, pp.18–19 (PDF pp.20–21)): the eleven nominal floor costs `a, …, k`, the
six effective chord coordinates `x, y, z, u, v, w`, the positive parameter `α`, and the two
pendant costs `L_y`, `L_z`.

**Formalization Note.** `y` and `z` are *effective* coordinates: the physical chords `B`, `C`
cost `y − L_y` and `z − L_z` (`physChord`). -/
structure Params where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ
  e : ℚ
  f : ℚ
  g : ℚ
  h : ℚ
  i : ℚ
  j : ℚ
  k : ℚ
  x : ℚ
  y : ℚ
  z : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  α : ℚ
  Ly : ℚ
  Lz : ℚ

namespace Params

/-- The thirteen nominal floor costs, indexed `0, …, 10 ↦ a, …, k`, `11 ↦ L_y` (pendant `Y`),
`12 ↦ L_z` (pendant `Z`) (§3, p.4 (PDF p.6)). -/
def nominal (p : Params) : Fin 13 → ℚ :=
  ![p.a, p.b, p.c, p.d, p.e, p.f, p.g, p.h, p.i, p.j, p.k, p.Ly, p.Lz]

/-- The six physical chord costs of the owners `A, …, F`: `x, y − L_y, z − L_z, u, v, w`
(§3, p.4 (PDF p.6)). -/
def physChord (p : Params) : Fin 6 → ℚ :=
  ![p.x, p.y - p.Ly, p.z - p.Lz, p.u, p.v, p.w]

/-- `S = a + ⋯ + k + L_y + L_z` (§3, p.4). -/
def S (p : Params) : ℚ :=
  p.a + p.b + p.c + p.d + p.e + p.f + p.g + p.h + p.i + p.j + p.k + p.Ly + p.Lz

/-- `C_Σ = x + y + z + u + v + w − L_y − L_z`, the total physical chord cost (§3, p.4). -/
def CSigma (p : Params) : ℚ := p.x + p.y + p.z + p.u + p.v + p.w - p.Ly - p.Lz

/-- `S_rec = a + b + j + k + L_y + L_z` (§3, p.4). -/
def Srec (p : Params) : ℚ := p.a + p.b + p.j + p.k + p.Ly + p.Lz

/-- `U_fix = S − S_rec` (§3, p.4). -/
def Ufix (p : Params) : ℚ := p.S - p.Srec

/-- `B_rec = S_rec / α` (§3, p.4). -/
def Brec (p : Params) : ℚ := p.Srec / p.α

/-- `L(η) = (S + C_Σ)/(S − α)` (§3, p.6 (PDF p.8); §A.4, p.18 (PDF p.20)). This is **not** the
constant `L` of Theorem 3.1, which is `Lconst`. -/
def Leta (p : Params) : ℚ := (p.S + p.CSigma) / (p.S - p.α)

/-- `(1 − t)·η₀ + t·η₁`, coordinatewise. -/
def lerp (p q : Params) (t : ℚ) : Params where
  a := (1 - t) * p.a + t * q.a
  b := (1 - t) * p.b + t * q.b
  c := (1 - t) * p.c + t * q.c
  d := (1 - t) * p.d + t * q.d
  e := (1 - t) * p.e + t * q.e
  f := (1 - t) * p.f + t * q.f
  g := (1 - t) * p.g + t * q.g
  h := (1 - t) * p.h + t * q.h
  i := (1 - t) * p.i + t * q.i
  j := (1 - t) * p.j + t * q.j
  k := (1 - t) * p.k + t * q.k
  x := (1 - t) * p.x + t * q.x
  y := (1 - t) * p.y + t * q.y
  z := (1 - t) * p.z + t * q.z
  u := (1 - t) * p.u + t * q.u
  v := (1 - t) * p.v + t * q.v
  w := (1 - t) * p.w + t * q.w
  α := (1 - t) * p.α + t * q.α
  Ly := (1 - t) * p.Ly + t * q.Ly
  Lz := (1 - t) * p.Lz + t * q.Lz

end Params

/-- The constant `L = 7808358178989/3195649632469 = 2.44343375433…` of Theorem 3.1 (p.3
(PDF p.5)). -/
def Lconst : ℚ := 7808358178989 / 3195649632469

/-- The common denominator `D′₀ = 33964062239365007131388227765376` of §A.5 (p.18 (PDF p.20)). -/
def Dprime0 : ℚ := 33964062239365007131388227765376

/-- The common denominator `D′₁ = 6391299264938` of §A.5 (p.18 (PDF p.20)). -/
def Dprime1 : ℚ := 6391299264938

/-- The endpoint vector `η₀` of §A.5 (pp.18–19 (PDF pp.20–21)): the column `D′₀η₀` of the integer
table, divided by `D′₀`. -/
def eta0 : Params where
  a := 4776604912883050355419104922560 / Dprime0
  b := 4616724305271316998508831255416 / Dprime0
  c := 3082116316201910351071885475508 / Dprime0
  d := 3510828590128607143599467753064 / Dprime0
  e := 4455191811873660979622295753460 / Dprime0
  f := 1734349326213648179165605503084 / Dprime0
  g := 1138186525081879269139176433860 / Dprime0
  h := 5601277750527803632473107451720 / Dprime0
  i := 1472820946424841137004875980080 / Dprime0
  j := 4589221384445804646537398860944 / Dprime0
  k := 3116400438020963509532522880864 / Dprime0
  x := 7389202735445562585257103462329 / Dprime0
  y := 6267615390989553094554919712039 / Dprime0
  z := 7236777462328553094031200360113 / Dprime0
  u := 4561126643072336086890860909869 / Dprime0
  v := 5875538626052778666072564094291 / Dprime0
  w := 4973317274124072074449493339951 / Dprime0
  α := 7518952521427611480855439443074 / Dprime0
  Ly := 10617278956154779957321420000 / Dprime0
  Lz := 28650134622469563736615234656 / Dprime0

/-- The endpoint vector `η₁` of §A.5 (pp.18–19 (PDF pp.20–21)): the column `D′₁η₁` of the integer
table, divided by `D′₁`. Its pendant cost `L_y` is `0`, so `η₁` itself is never a game. -/
def eta1 : Params where
  a := 958605171768 / Dprime1
  b := 958605171768 / Dprime1
  c := 680321128842 / Dprime1
  d := 749990809728 / Dprime1
  e := 768099034710 / Dprime1
  f := 649359820170 / Dprime1
  g := 72138815316 / Dprime1
  h := 1229613111936 / Dprime1
  i := 324413289324 / Dprime1
  j := 936868380804 / Dprime1
  k := 612455091480 / Dprime1
  x := 1539031866156 / Dprime1
  y := 1299716485920 / Dprime1
  z := 1502803881216 / Dprime1
  u := 975498195609 / Dprime1
  v := 1221433584858 / Dprime1
  w := 1137762518373 / Dprime1
  α := 1550239583748 / Dprime1
  Ly := 0 / Dprime1
  Lz := 1069022840 / Dprime1

/-- The parameter segment `η(t) = (1 − t)η₀ + tη₁` (§A.5, p.18 (PDF p.20); the construction uses
it for rational `0 ≤ t < 1`). -/
def etaAt (t : ℚ) : Params := Params.lerp eta0 eta1 t

end PoSUndirected


