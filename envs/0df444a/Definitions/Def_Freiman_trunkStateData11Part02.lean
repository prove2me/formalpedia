-- Prove2me | Definitions.Def_Freiman_trunkStateData11Part02
-- name    : Freiman_trunkStateData11Part02
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:18:55.170087+00:00
-- url     : https://prove2.me/theorems/6511c597-3c24-45a5-a643-dca94ec7a170
-- title:
--   trunkStateData11Part02
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkModel

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Freiman
def trunkStateData11Part02 : List TrunkGroup := [
    ⟨4,[17],0,[(-1,(.pair 7598))]⟩,
    ⟨4,[23],2,[(0,(.pair 7262)),(1,(.pair 7262)),(2,(.pair 7262)),(3,(.pair 7262))]⟩,
    ⟨4,[23],5,[(0,(.pair 7485)),(1,(.pair 7599)),(2,(.pair 7600)),(3,(.pair 7601))]⟩,
    ⟨4,[23],7,[(0,(.pair 7270)),(1,(.pair 7270)),(2,(.pair 7270)),(3,(.pair 7270)),(4,(.pair 7270)),(5,(.pair 7270)),(6,(.pair 7270)),(7,(.pair 7270)),(8,(.pair 7270)),(9,(.pair 7270)),(10,(.pair 7270)),(11,(.pair 7270)),(12,(.pair 7270)),(13,(.pair 7270)),(14,(.pair 7270)),(15,(.pair 7270)),(16,(.pair 7270)),(17,(.pair 7270)),(18,(.pair 7270)),(19,(.pair 7270)),(20,(.pair 7270)),(21,(.pair 7270)),(22,(.pair 7270)),(23,(.pair 7270)),(24,(.pair 7270))]⟩,
    ⟨4,[23],9,[(0,(.pair 7489)),(1,(.pair 7602)),(2,(.pair 7603)),(3,(.pair 7604)),(4,(.pair 7605)),(5,(.pair 7489)),(6,(.pair 7602)),(7,(.pair 7603)),(8,(.pair 7604)),(9,(.pair 7605)),(10,(.pair 7494)),(11,(.pair 7606)),(12,(.pair 7606)),(13,(.pair 7606)),(14,(.pair 7605)),(15,(.pair 7496)),(16,(.pair 7607)),(17,(.pair 7607)),(18,(.pair 7607)),(19,(.pair 7607)),(20,(.pair 7498)),(21,(.pair 7608)),(22,(.pair 7608)),(23,(.pair 7608)),(24,(.pair 7608))]⟩,
    ⟨4,[23],12,[(0,(.pair 7609)),(1,(.pair 7610)),(2,(.pair 7611)),(3,(.pair 7612)),(4,(.pair 7609)),(5,(.pair 7610)),(6,(.pair 7613)),(7,(.pair 7612)),(8,(.pair 7609)),(9,(.pair 7610)),(10,(.pair 7611)),(11,(.pair 7612)),(12,(.pair 7609)),(13,(.pair 7610)),(14,(.pair 7614)),(15,(.pair 7612))]⟩,
    ⟨4,[23],15,[(0,(.pair 7615)),(1,(.pair 7616)),(2,(.pair 7617)),(3,(.pair 7618))]⟩,
    ⟨4,[23],17,[(0,(.pair 7619)),(1,(.pair 7619)),(2,(.pair 7619)),(3,(.pair 7619)),(4,(.pair 7619)),(5,(.pair 7620)),(6,(.pair 7620)),(7,(.pair 7620)),(8,(.pair 7620)),(9,(.pair 7620)),(10,(.pair 7621)),(11,(.pair 7622)),(12,(.pair 7623)),(13,(.pair 7622)),(14,(.pair 7624)),(15,(.pair 7621)),(16,(.pair 7625)),(17,(.pair 7625)),(18,(.pair 7625)),(19,(.pair 7625)),(20,(.pair 7621)),(21,(.pair 7622)),(22,(.pair 7623)),(23,(.pair 7622)),(24,(.pair 7624))]⟩,
    ⟨4,[23],19,[(0,(.pair 7626)),(1,(.pair 7627)),(2,(.pair 7626)),(3,(.pair 7628)),(4,(.pair 7629)),(5,(.pair 7626)),(6,(.pair 7627)),(7,(.pair 7626)),(8,(.pair 7628)),(9,(.pair 7629)),(10,(.pair 7630)),(11,(.pair 7630)),(12,(.pair 7630)),(13,(.pair 7630)),(14,(.pair 7629)),(15,(.pair 7631)),(16,(.pair 7631)),(17,(.pair 7631)),(18,(.pair 7631)),(19,(.pair 7631)),(20,(.pair 7632)),(21,(.pair 7632)),(22,(.pair 7632)),(23,(.pair 7632)),(24,(.pair 7632))]⟩,
    ⟨4,[23],22,[(0,(.pair 7633)),(1,(.pair 7633)),(2,(.pair 7634)),(3,(.pair 7634)),(4,(.pair 7635)),(5,(.pair 7636)),(6,(.pair 7635)),(7,(.pair 7637)),(8,(.pair 7635)),(9,(.pair 7636))]⟩,
    ⟨4,[23],24,[(0,(.pair 7638)),(1,(.pair 7639)),(2,(.pair 7638)),(3,(.pair 7640)),(4,(.pair 7641)),(5,(.pair 7638)),(6,(.pair 7639)),(7,(.pair 7638)),(8,(.pair 7640)),(9,(.pair 7641)),(10,(.pair 7642)),(11,(.pair 7642)),(12,(.pair 7642)),(13,(.pair 7642)),(14,(.pair 7641)),(15,(.pair 7643)),(16,(.pair 7643)),(17,(.pair 7643)),(18,(.pair 7643)),(19,(.pair 7643)),(20,(.pair 7644)),(21,(.pair 7644)),(22,(.pair 7644)),(23,(.pair 7644)),(24,(.pair 7644))]⟩,
    ⟨4,[23],27,[(0,(.pair 7645)),(1,(.pair 7645)),(2,(.pair 7645)),(3,(.pair 7645)),(4,(.pair 7645)),(5,(.pair 7646)),(6,(.pair 7646)),(7,(.pair 7646)),(8,(.pair 7646)),(9,(.pair 7646)),(10,(.pair 7647)),(11,(.pair 7648)),(12,(.pair 7649)),(13,(.pair 7648)),(14,(.pair 7650)),(15,(.pair 7647)),(16,(.pair 7651)),(17,(.pair 7651)),(18,(.pair 7651)),(19,(.pair 7651)),(20,(.pair 7647)),(21,(.pair 7648)),(22,(.pair 7649)),(23,(.pair 7648)),(24,(.pair 7650))]⟩,
    ⟨4,[23],29,[(0,(.pair 7652)),(1,(.pair 7653)),(2,(.pair 7652)),(3,(.pair 7653)),(4,(.pair 7654)),(5,(.pair 7653)),(6,(.pair 7655)),(7,(.pair 7655)),(8,(.pair 7656)),(9,(.pair 7656))]⟩,
    ⟨4,[23],32,[(0,(.pair 7262)),(1,(.pair 7270)),(2,(.pair 7262)),(3,(.pair 7270)),(4,(.pair 7262)),(5,(.pair 7282)),(6,(.pair 7262)),(7,(.pair 7443))]⟩,
    ⟨4,[23],34,[(0,(.pair 7270)),(1,(.pair 7270)),(2,(.pair 7657)),(3,(.pair 7657)),(4,(.pair 7270)),(5,(.pair 7270)),(6,(.pair 7658)),(7,(.pair 7659)),(8,(.pair 7270)),(9,(.pair 7270)),(10,(.pair 7660)),(11,(.pair 7661)),(12,(.pair 7270)),(13,(.pair 7270)),(14,(.pair 7662)),(15,(.pair 7663)),(16,(.pair 7270)),(17,(.pair 7270)),(18,(.pair 7664)),(19,(.pair 7665))]⟩,
    ⟨4,[23],35,[(0,(.pair 7666)),(1,(.pair 7667)),(2,(.pair 7668)),(3,(.pair 7669)),(4,(.pair 7666)),(5,(.pair 7667)),(6,(.pair 7668)),(7,(.pair 7669)),(8,(.pair 7670)),(9,(.pair 7671)),(10,(.pair 7672)),(11,(.pair 7673)),(12,(.pair 7674)),(13,(.pair 7675)),(14,(.pair 7674)),(15,(.pair 7676)),(16,(.pair 7677)),(17,(.pair 7678)),(18,(.pair 7677)),(19,(.pair 7679))]⟩,
    ⟨4,[23],36,[(0,(.pair 7680)),(1,(.pair 7570)),(2,(.pair 7681)),(3,(.pair 7682)),(4,(.pair 7680)),(5,(.pair 7683)),(6,(.pair 7684)),(7,(.pair 7685))]⟩,
    ⟨4,[23],38,[(0,(.pair 7574)),(1,(.pair 7575)),(2,(.pair 7686)),(3,(.pair 7687)),(4,(.pair 7578)),(5,(.pair 7579)),(6,(.pair 7688)),(7,(.pair 7689)),(8,(.pair 7582)),(9,(.pair 7690)),(10,(.pair 7691)),(11,(.pair 7691)),(12,(.pair 7584)),(13,(.pair 7585)),(14,(.pair 7692)),(15,(.pair 7692))]⟩,
    ⟨4,[23],39,[(0,(.pair 7693)),(1,(.pair 7694)),(2,(.pair 7693)),(3,(.pair 7695))]⟩,
    ⟨4,[23],40,[(0,(.pair 7696)),(1,(.pair 7697)),(2,(.pair 7696)),(3,(.pair 7698))]⟩,
    ⟨4,[29],0,[(-1,(.pair 7699))]⟩
  ]
end Freiman


