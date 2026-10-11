-- Prove2me | Definitions.Def_intmul_round8_certs_extra
-- name    : intmul_round8_certs_extra
-- status  : Definition
-- author  : @chstdu
-- created : 2026-10-10T15:23:52.439457+00:00
-- url     : https://prove2.me/theorems/dfbc7a6a-d701-4658-a783-1d3df0bfd4a8
-- title:
--   Round-eight certificate checkers: expUp, momentExpOK, stopOK
-- statement:
--   The round-eight additions to the integer-multiplication κ-certificate checkers (Jain, repository `integer-mult-kappa`, file `lean/Round8.lean`). The function `expUp` is a rational upper bound for $e^x$ on $0 \le x < 1$ obtained from the power series with a geometric tail bound. On top of it, `momentExpOK` is the exp-form moment condition of the linear-network analysis: for every width class $(w, n)$ of a histogram, $w < m$ and $a\,L_w < 4$ with $L_w = \operatorname{lnUp}(m/w)$, and $\sum n\,w\,e^{a L_w} / m < W$. Finally `stopOK` checks a stopped saving: $a_b = (1-\theta)\,a + \theta\,a_{\text{old}}$ exactly, and $a_b < \theta$.
-- source:
--   Swapnil Jain, integer-mult-kappa, https://github.com/Swapnil-jain/integer-mult-kappa, file lean/Round8.lean (expUp, momentExpOK, stopOK).

/-
  Round-eight additions to the integer-multiplication certificate checkers: an exponential
upper bound expUp, the exp-form moment condition momentExpOK, and the stopped-saving
guard stopOK (Jain, integer-mult-kappa, lean/Round8.lean).
-/

import Definitions.Def_intmul_certs_arith

namespace IntMul.Certs

def expUp (x : Q) : Q :=
  qadd (qadd (qadd (1, 1) x) (qdiv (qmul x x) (2, 1)))
    (qdiv (qmul x (qmul x x)) (qmul (6, 1) (qsub (1, 1) (qdiv x (4, 1)))))

-- moment bound through exp: every a * L_w < 4, every w < m, and sum n w E(a L_w) / m < W
def momentExpOK (h : List (Nat × Nat)) (a : Q) (m W : Nat) : Bool :=
  let step := fun (acc : Bool × Q) (p : Nat × Nat) =>
    let w := p.1; let n := p.2
    let al := qmul a (lnUp (m, w))
    let ok := acc.1 && (w < m) && qlt al (4, 1)
    if ok then (true, qadd acc.2 (qdiv (qmul (n * w, 1) (expUp al)) (m, 1))) else (false, acc.2)
  let r := h.foldl step (true, (0, 1))
  r.1 && qlt r.2 (W, 1)

-- stopped saving: ab = (1 - theta) a + theta aold, and ab < theta
def stopOK (a aold theta ab : Q) : Bool :=
  let v := qadd (qmul (qsub (1, 1) theta) a) (qmul theta aold)
  v.1 * ab.2 == ab.1 * v.2 && qlt ab theta

-- bit interchange, opposite bank orders (one-run histogram, moment at a*)

end IntMul.Certs


