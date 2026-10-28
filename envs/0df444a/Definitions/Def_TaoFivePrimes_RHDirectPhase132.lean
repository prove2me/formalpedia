-- Prove2me | Definitions.Def_TaoFivePrimes_RHDirectPhase132
-- name    : TaoFivePrimes_RHDirectPhase132
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:34:10.601244+00:00
-- url     : https://prove2.me/theorems/5e1dc994-11c3-48ba-85fd-c43cb3642f82
-- title:
--   Fixed-point oscillatory phase candidates at height 132
-- statement:
--   Let $D=10^{200}$. Store a pair of integers $p_0=(a,b)$ as a proposed fixed-point approximation to $e^{99i/256}$. For pairs of integers define
--
--   $$
--   (a,b)\star(c,d)=
--   \left(\left\lfloor\frac{ac-bd}{D}\right\rfloor,
--   \left\lfloor\frac{ad+bc}{D}\right\rfloor\right).
--   $$
--
--   Let $p_{n+1}=p_n\star p_n$, $r_0=p_5$, and $r_{j+1}=r_j\star p_6$. The candidate for panel $j$ is $(r_{j,1}+ir_{j,2})/D$. The stored integers and recurrences are data: their accuracy and any zero-location conclusion are separate statements.
-- source:
--   Fixed-point candidate data for the direct oscillatory theta/Mellin quadrature framework due to Gabewhigham and sometik179.

/- Candidate fixed-point phases at height 132.
No accuracy or zero-location assertion is part of this definition. -/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace RHDirectPhase132

def scale : ℤ := 10^200
def seed : ℤ × ℤ := (92615157179669613016592591668971345137937463649480877392953487874102826124243604285377482092984521936184545732180454262832386360915017189683406929799503142607936037592738748163892925885538344905919673, 37715151604959672127796761208501566546996855780943190898421677277626014933111559513023451348104982842570602189708664073190113086786283028956182803726784019631304512812295109494020801823595264949273772)

def multiply (x y : ℤ × ℤ) : ℤ × ℤ :=
  ((x.1*y.1-x.2*y.2)/scale, (x.1*y.2+x.2*y.1)/scale)

def squares : ℕ → ℤ × ℤ
  | 0 => seed
  | n+1 => multiply (squares n) (squares n)

def panels : ℕ → ℤ × ℤ
  | 0 => squares 5
  | n+1 => multiply (panels n) (squares 6)

noncomputable def asComplex (z : ℤ × ℤ) : ℂ :=
  ((z.1:ℂ)+Complex.I*(z.2:ℂ))/(10^200:ℂ)

end RHDirectPhase132


